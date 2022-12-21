use crate::{config, matrix_common, protocol};
use matrix_sdk::config::SyncSettings;
use matrix_sdk::Client;
use ruma_client_api::to_device::send_event_to_device;
use ruma_client_api::{filter, sync::sync_events};
use std::convert::TryFrom;
use std::str::FromStr;
use std::time::Duration;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    ConfigError(#[from] config::Error),

    #[error(transparent)]
    RumaError(#[from] matrix_sdk::Error),

    #[error(transparent)]
    RumaIdentifierError(#[from] ruma_identifiers::Error),

    #[error(transparent)]
    MatrixUriParseError(#[from] MatrixUriParseError),

    #[error("Matrix uri does not have a room id: {}", .0)]
    MatrixUriIsNotRoomIdError(String),

    #[error("Matrix uri does not have event id: {}", .0)]
    MatrixUriMissingEventIdError(String),

    #[error("Event is not a message: {}", .0)]
    NotAMessageEventError(String),

    #[error(transparent)]
    MatrixHttpError(#[from] matrix_sdk::HttpError),

    #[error(transparent)]
    MatrixCommonError(#[from] matrix_common::Error),

    #[error("Matrix room not found: {}", .0)]
    NoSuchRoomError(String),

    #[error(transparent)]
    SerdeJsonError(#[from] serde_json::Error),

    #[error(transparent)]
    MatrixClientbuildError(#[from] matrix_sdk::ClientBuildError),

    #[error(transparent)]
    IdParseError(#[from] ruma::IdParseError),

    #[error(transparent)]
    OpenStoreError(#[from] matrix_sdk_sled::OpenStoreError),
}

#[derive(Error, Debug)]
pub struct MatrixUriParseError(matrix_uri::MatrixUriParseError);

impl std::fmt::Display for MatrixUriParseError {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        fmt.write_fmt(format_args!("Matrix URI parse error: {:?}", self.0))
    }
}

fn mxid_uri_from_mxid(mxid: &matrix_uri::MatrixId) -> String {
    // I don't understand when the sigil is or isn't there..
    match mxid.id_type {
        matrix_uri::IdType::RoomAlias => format!("{}{}", mxid.id_type.to_sigil(), mxid.body),
        _ => String::from(mxid.body.clone()),
    }
}

#[rustfmt::skip::macros(select)]
pub async fn download(
    config: config::Config,
    state_dir: &str,
    urls: Vec<&str>,
) -> Result<(), Error> {
    let session = config.get_matrix_session()?;

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
        //.timeout(Duration::from_millis(1000))
        .full_state(true);
    let client = Client::builder()
        .server_name(session.user_id.server_name())
        .sled_store(state_dir, None)?
        .build()
        .await?;
    client.restore_login(session).await?;

    let first_sync_response = client.sync_once(sync_settings.clone()).await.unwrap();

    let uri = matrix_uri::MatrixUri::from_str(urls[0]).map_err(|x| MatrixUriParseError(x))?;
    let mxid = mxid_uri_from_mxid(&uri.mxid);
    let room_id = match uri.mxid.id_type {
        matrix_uri::IdType::RoomId => {
            <&matrix_sdk::ruma::RoomId>::try_from(mxid.as_str())?.to_owned()
        }
        _ => {
            return Err(Error::MatrixUriIsNotRoomIdError(format!(
                "{:?}",
                uri.mxid.id_type
            )))
        }
    };
    let event_id = match uri.child_mxid {
        Some(child_mxid) => match child_mxid.id_type {
            matrix_uri::IdType::EventId => {
                <&matrix_sdk::ruma::EventId>::try_from(mxid_uri_from_mxid(&child_mxid).as_str())?
                    .to_owned()
            }
            _ => {
                return Err(Error::MatrixUriMissingEventIdError(format!(
                    "{:?}",
                    child_mxid.id_type
                )))
            }
        },
        _ => {
            return Err(Error::MatrixUriMissingEventIdError(format!(
                "{:?}",
                uri.mxid.id_type
            )))
        }
    };

    // needed to populate Client internal data
    //let _rooms = matrix_common::get_joined_rooms(&client).await?;
    // let room_id = <&matrix_sdk::ruma::RoomId>::try_from(room_id.as_str())?.to_owned();
    let room = client
        .get_joined_room(&room_id)
        .ok_or(Error::NoSuchRoomError(String::from(room_id.as_str())))?;

    let event = room.event(event_id.as_ref()).await?;

    let offer = serde_json::from_str::<protocol::SyncOffer>(event.event.json().get())?;
    println!("offer: {offer:?}");

    let peer_user_id = offer.sender().to_owned();

    let txn_id = ruma::TransactionId::new();
    use ruma::events::AnyToDeviceEventContent;
    use ruma::serde::Raw;
    use ruma_common::to_device::DeviceIdOrAllDevices;
    use std::collections::BTreeMap;
    type Foo = BTreeMap<DeviceIdOrAllDevices, Raw<AnyToDeviceEventContent>>;
    let mut messages = send_event_to_device::v3::Messages::new();
    let all = DeviceIdOrAllDevices::AllDevices;

    let request_session = protocol::RequestSessionEventContent {
        webrtc_offer: protocol::WebRTCOffer {
            offer: String::from("moi"),
        },
    };

    let request_session_event: Raw<AnyToDeviceEventContent> =
        Raw::from_json(serde_json::value::to_raw_value(&request_session)?);

    let values: Foo = vec![(all, request_session_event)].into_iter().collect();

    messages.insert(peer_user_id, values);
    let request = send_event_to_device::v3::Request::new_raw(
        "fi.variaattori.mxrxtx.request_session",
        &txn_id,
        messages,
    );
    client.send(request, None).await?;

    let sync_settings = SyncSettings::default()
        .filter(sync_events::v3::Filter::FilterDefinition(filter_def))
        .timeout(Duration::from_millis(10000))
        .token(first_sync_response.next_batch);
    client
        .sync_with_callback(sync_settings, |response| async move {
            // println!("got: {:?}", response);
            let mut accepted = false;
            for event in response.to_device.events {
                match serde_json::from_str::<protocol::AcceptSessionEvent>(event.json().get()) {
                    Ok(value) => {
                        println!("Cool: {value:?}");
                        accepted = true;
                    }
                    Err(err) => println!("Not cool: {err:?}"),
                }
            }

            if accepted {
                println!("Doing some transferring maybe");
            }
            // let channel = sync_channel;

            // for (room_id, room) in response.rooms.join {
            //     for event in room.timeline.events {
            //         channel.send(event).await.unwrap();
            //     }
            // }
            // println!("Got sync response {:?}, breaking out", response);

            // matrix_sdk::LoopCtrl::Break
            matrix_sdk::LoopCtrl::Continue
        })
        .await?;

    Ok(())
}
