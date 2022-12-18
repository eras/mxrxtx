use crate::{config, matrix_common, protocol};
use matrix_sdk::config::SyncSettings;
use matrix_sdk::Client;
use ruma_client_api::to_device::send_event_to_device;
use ruma_client_api::{filter, sync::sync_events};
use std::convert::TryFrom;
use std::time::Duration;
use thiserror::Error;
use tokio::select;

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    ConfigError(#[from] config::Error),

    #[error(transparent)]
    RumaError(#[from] matrix_sdk::Error),

    #[error(transparent)]
    RumaIdentifierError(#[from] ruma_identifiers::Error),

    #[error(transparent)]
    MatrixHttpError(#[from] matrix_sdk::HttpError),

    #[error(transparent)]
    MatrixCommonError(#[from] matrix_common::Error),

    #[error("Matrix room not found: {}", .0)]
    NoSuchRoomError(String),

    #[error("Multiple matrix rooms matching pattern found: {}", .0)]
    MultipleRoomNameMatchesError(String),

    #[error("Room id/name must start with either ! or #: {}", .0)]
    RoomNameError(String),

    #[error(transparent)]
    MatrixClientbuildError(#[from] matrix_sdk::ClientBuildError),

    #[error(transparent)]
    IdParseError(#[from] ruma::IdParseError),

    #[error(transparent)]
    OpenStoreError(#[from] matrix_sdk_sled::OpenStoreError),
}

enum RoomType {
    RoomId,
    RoomName,
}

impl RoomType {
    fn classify(name: &str) -> Result<RoomType, Error> {
        let ch0 = name.chars().next().unwrap();
        if ch0 == '!' {
            Ok(RoomType::RoomId)
        } else if ch0 == '#' {
            Ok(RoomType::RoomName)
        } else {
            Err(Error::RoomNameError(name.to_string()))
        }
    }
}

#[rustfmt::skip::macros(select)]
pub async fn offer(
    config: config::Config,
    state_dir: &str,
    room: &str,
    files: Vec<&str>,
) -> Result<(), Error> {
    dbg!();
    let session = config.get_matrix_session()?;
    dbg!();

    let mut empty_room_event_filter = filter::RoomEventFilter::empty();
    empty_room_event_filter.limit = Some(From::from(1u32));
    empty_room_event_filter.rooms = Some(&[]);
    empty_room_event_filter.lazy_load_options = filter::LazyLoadOptions::Enabled {
        include_redundant_members: false,
    };

    let mut no_types_filter = filter::Filter::empty();
    no_types_filter.types = Some(&[]);
    let mut filter_def = filter::FilterDefinition::empty();
    filter_def.presence = no_types_filter.clone();
    filter_def.account_data = no_types_filter.clone();
    filter_def.room.include_leave = false;
    filter_def.room.account_data = empty_room_event_filter.clone();
    filter_def.room.timeline = empty_room_event_filter.clone();
    filter_def.room.ephemeral = empty_room_event_filter.clone();
    filter_def.room.state = empty_room_event_filter.clone();

    let sync_settings = SyncSettings::default()
        .filter(sync_events::v3::Filter::FilterDefinition(
            filter_def.clone(),
        ))
        //.timeout(Duration::from_millis(10000))
        .full_state(true);
    let client = Client::builder()
        .server_name(session.user_id.server_name())
        .sled_store(state_dir, None)?
        .build()
        .await?;
    client.restore_login(session).await?;

    let user_id = client
        .user_id()
        .expect("User id should be set at this point");
    let user_id = ruma_common::UserId::parse(user_id.as_str())?;

    let first_sync_response = client.sync_once(sync_settings.clone()).await.unwrap();

    let room = match RoomType::classify(room)? {
        RoomType::RoomId => {
            let room_id = <&matrix_sdk::ruma::RoomId>::try_from(room)?.to_owned();
            client
                .get_joined_room(&room_id)
                .ok_or(Error::NoSuchRoomError(String::from(room)))?
        }
        RoomType::RoomName => {
            let rooms = client.joined_rooms();
            println!("rooms: {:?}", rooms);
            let room_alias = client
                .resolve_room_alias(&matrix_sdk::ruma::RoomAliasId::parse(room)?)
                .await
                .unwrap();
            let matching: Vec<&matrix_sdk::room::Joined> = rooms
                .iter()
                .filter(|&joined_room| joined_room.room_id() == room_alias.room_id)
                .collect();
            if matching.len() == 1 {
                matching[0].clone()
            } else if matching.len() > 1 {
                return Err(Error::MultipleRoomNameMatchesError(String::from(room)));
            } else {
                return Err(Error::NoSuchRoomError(String::from(room)));
            }
        }
    };
    println!("room: {:?}", room);

    let files: Vec<protocol::File> = files
        .iter()
        .map(|file| protocol::File {
            name: file.to_string(),
            content_type: String::from("application/octet-stream"),
            size: 0u64,
        })
        .collect();

    let offer = protocol::OfferContent { files: files };

    // let content = ruma_events::room::message::MessageType::new(EVENT_TYPE_OFFER, data).unwrap(); // should work always

    // let content = RoomMessageEventContent::new(content);

    let event_id = room
        .send(offer, Some(&ruma::TransactionId::new()))
        .await?
        .event_id;

    let uri = matrix_uri::MatrixUri::new(
        matrix_uri::MatrixId::new(
            matrix_uri::IdType::RoomId,
            String::from(room.room_id().as_str()),
        ),
        Some(matrix_uri::MatrixId::new(
            matrix_uri::IdType::EventId,
            String::from(event_id.as_str()),
        )),
        None,
        None,
        None,
    )
    .unwrap();

    println!(
        "Offer for {} started; press ctrl-c to redact",
        uri.matrix_uri_string()
    );
    let ctrl_c = tokio::signal::ctrl_c();

    let sync_settings = SyncSettings::default()
        .filter(sync_events::v3::Filter::FilterDefinition(filter_def))
        .timeout(Duration::from_millis(10000))
        .token(first_sync_response.next_batch);
    select! {
	_done = ctrl_c => {
	    ()
	}
	_done = {
	    client
	    .sync_with_callback(sync_settings, |response| async {
		let mut requested = false;
                for event in response.to_device.events {
		    match serde_json::from_str::<protocol::RequestSessionEvent>(event.json().get()) {
			Ok(value) => {
			    println!("Cool: {value:?}");
			    requested = true;
			}
			Err(err) => println!("Not cool: {err:?}"),
		    }
                }

		if requested {
		    let accept_session = protocol::RequestSessionEventContent {
			session_info: protocol::SessionInfo {
			    webrtc_ice: String::from("heihei"),
			},
		    };

		    let accept_session_event: Raw<AnyToDeviceEventContent> =
			Raw::from_json(serde_json::value::to_raw_value(&accept_session).unwrap());

		    use ruma::events::AnyToDeviceEventContent;
		    use ruma::serde::Raw;
		    use ruma_common::to_device::DeviceIdOrAllDevices;
		    use std::collections::BTreeMap;
		    let all = DeviceIdOrAllDevices::AllDevices;
		    let mut messages = send_event_to_device::v3::Messages::new();
		    type Foo = BTreeMap<DeviceIdOrAllDevices, Raw<AnyToDeviceEventContent>>;
		    let values: Foo = vec![(all, accept_session_event)].into_iter().collect();

		    let txn_id = ruma::TransactionId::new();
		    messages.insert(user_id.clone(), values);
		    let request = send_event_to_device::v3::Request::new_raw(
			"fi.variaattori.mxrxtx.accept_session",
			&txn_id,
			messages,
		    );
		    client.send(request, None).await.unwrap(); // TODO
		}

	        // matrix_sdk::LoopCtrl::Break
	        matrix_sdk::LoopCtrl::Continue
	})} => {
		()
	    }
    }

    println!("Redacting offer");
    room.redact(
        &event_id,
        Some("Offer expired"),
        Some(ruma::TransactionId::new()),
    )
    .await?;
    println!("Done");

    Ok(())
}
