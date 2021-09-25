use crate::config;
use ruma::api::client::r0::{sync::sync_events, filter};
use ruma_events::{
    AnyMessageEventContent,
    room::message::MessageEventContent,
};
use matrix_sdk::uuid::Uuid;
use std::convert::TryFrom;
use std::time::Duration;
use thiserror::Error;
use tokio::select;

const EVENT_TYPE_OFFER: &str = "fi.variaattori.direct_transfer.offer";

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

    #[error("Matrix room not found: {}", .0)]
    NoSuchRoomError(String),

    #[error("Multiple matrix rooms matching pattern found: {}", .0)]
    MultipleRoomNameMatchesError(String),

    #[error("Room id/name must start with either ! or #: {}", .0)]
    RoomNameError(String),
}

async fn get_joined_rooms(client: &matrix_sdk::Client) -> Result<Vec<matrix_sdk::room::Joined>, Error> {
    let mut empty_room_event_filter = filter::RoomEventFilter::empty();
    empty_room_event_filter.limit             = Some(From::from(1u32));
    empty_room_event_filter.rooms             = Some(&[]);
    empty_room_event_filter.lazy_load_options =
	filter::LazyLoadOptions::Enabled { include_redundant_members: false };

    let mut no_types_filter = filter::Filter::empty();
    no_types_filter.types = Some(&[]);

    let mut filter_def = filter::FilterDefinition::empty();
    filter_def.presence           = no_types_filter.clone();
    filter_def.account_data       = no_types_filter.clone();
    filter_def.room.include_leave = false;
    filter_def.room.account_data  = empty_room_event_filter.clone();
    filter_def.room.timeline      = empty_room_event_filter.clone();
    filter_def.room.ephemeral     = empty_room_event_filter.clone();
    filter_def.room.state         = empty_room_event_filter.clone();
    let sync_settings =
	matrix_sdk::SyncSettings::default()
	.filter(sync_events::Filter::FilterDefinition(filter_def))
	.timeout(Duration::from_millis(1000))
	.full_state(true);
    let _sync_response = client.sync_once(sync_settings).await?;
    Ok(client.joined_rooms())
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
pub async fn offer(config: config::Config,
		   room: &str,
		   files: Vec<&str>) -> Result<(), Error> {
    let session = config.get_matrix_session()?;
    let client = matrix_sdk::Client::new_from_user_id(session.user_id.clone()).await?;
    client.restore_login(session).await?;

    let rooms = get_joined_rooms(&client).await?;
    //println!("rooms: {:?}", rooms);
    let room =
	match RoomType::classify(room)? {
	    | RoomType::RoomId => {
		client.get_joined_room(&ruma::RoomId::try_from(room)?)
		    .ok_or(Error::NoSuchRoomError(String::from(room)))?
	    }
	    | RoomType::RoomName => {
		// TODO: seems the canonical aliases are empty, so no go
		let matching: Vec<&matrix_sdk::room::Joined> =
		    rooms.iter().filter(|&joined_room| {
			println!("canonical alias: {:?}", joined_room.canonical_alias());
			joined_room.canonical_alias().map_or(false, |x| x.alias() == room)
		    }).collect();
		if matching.len() == 1 {
		    matching[0].clone()
		} else if matching.len() > 1 {
		    return Err(Error::MultipleRoomNameMatchesError(String::from(room)))
		} else {
		    return Err(Error::NoSuchRoomError(String::from(room)))
		}
	    }
	};
    println!("room: {:?}", room);

    type JsonObject = serde_json::Map<String, serde_json::Value>;
    type JsonArray =  Vec<serde_json::Value>;

    use serde_json::Value::{String as JsonString, Object};

    let files_offer: JsonArray =
	files
	.iter()
	.map(|file| {
	    let obj: JsonObject =
		vec![
		    ("name".to_string()         , JsonString(file.to_string())),
		    ("content_type".to_string() , JsonString("application/octet-stream".to_string())),
		    ("size".to_string()         , serde_json::Value::Number(serde_json::Number::from(0u64))),
		]
		.into_iter()
		.collect();
	    Object(obj)
	})
	.collect();

    let data: JsonObject =
	vec![//("name".to_string(), JsonString(files.clone().join(", ").to_string())),
	     ("files".to_string(), serde_json::Value::Array(files_offer.clone())),
	]
	.into_iter()
	.collect();
    let data: JsonObject =
    	vec![("body".to_string(), JsonString(format!("File offer: {}", files.clone().join(", ")))),
    	     ("data".to_string(), Object(data))]
    	.into_iter()
    	.collect();

    let content = ruma_events::room::message::MessageType::new(EVENT_TYPE_OFFER, data).unwrap(); // should work always

    let content = AnyMessageEventContent::RoomMessage(
        MessageEventContent::new(content)
    );

    let txn_id = Uuid::new_v4();
    let event_id = room.send(content, Some(txn_id)).await?.event_id;

    println!("Offer started; press ctrl-c to redact");
    let ctrl_c = tokio::signal::ctrl_c();

    let mut empty_room_event_filter = filter::RoomEventFilter::empty();
    empty_room_event_filter.limit             = Some(From::from(1u32));
    empty_room_event_filter.rooms             = Some(&[]);
    empty_room_event_filter.lazy_load_options =
	filter::LazyLoadOptions::Enabled { include_redundant_members: false };

    let mut no_types_filter = filter::Filter::empty();
    no_types_filter.types = Some(&[]);
    let mut filter_def = filter::FilterDefinition::empty();
    filter_def.presence           = no_types_filter.clone();
    filter_def.account_data       = no_types_filter.clone();
    filter_def.room.include_leave = false;
    filter_def.room.account_data  = empty_room_event_filter.clone();
    filter_def.room.timeline      = empty_room_event_filter.clone();
    filter_def.room.ephemeral     = empty_room_event_filter.clone();
    filter_def.room.state         = empty_room_event_filter.clone();
    let sync_settings =
	matrix_sdk::SyncSettings::default()
	.filter(sync_events::Filter::FilterDefinition(filter_def))
	.timeout(Duration::from_millis(1000))
	.full_state(true);
    select! {
	_done = ctrl_c => {
	    ()
	}
	_done = client
	    .sync_with_callback(sync_settings, |response| async move {
	        // let channel = sync_channel;

	        // for (room_id, room) in response.rooms.join {
	        //     for event in room.timeline.events {
	        //         channel.send(event).await.unwrap();
	        //     }
	        // }
		println!("Got sync response {:?}, breaking out", response);

	        matrix_sdk::LoopCtrl::Break
	}) => {
		()
	    }
    }

    println!("Redacting offer");
    let txn_id = Uuid::new_v4();
    room.redact(&event_id, Some("Offer expired"), Some(txn_id)).await?;
    println!("Done");

    Ok(())
}
