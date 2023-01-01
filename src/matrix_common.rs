use matrix_sdk::{room::Joined, Client};
use ruma_client_api::{filter, sync::sync_events};
use std::convert::TryFrom;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
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

    #[error(transparent)]
    IdParseError(#[from] ruma::IdParseError),
}

enum RoomType {
    RoomId,
    RoomName,
}

impl RoomType {
    fn classify(name: &str) -> Result<RoomType, Error> {
        let ch0 = name
            .chars()
            .next()
            .expect("Room name should have at least one character");
        if ch0 == '!' {
            Ok(RoomType::RoomId)
        } else if ch0 == '#' {
            Ok(RoomType::RoomName)
        } else {
            Err(Error::RoomNameError(name.to_string()))
        }
    }
}

pub(crate) fn just_joined_rooms_filter<'a>() -> sync_events::v3::Filter<'a> {
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
    sync_events::v3::Filter::FilterDefinition(filter_def)
}

pub(crate) async fn get_joined_room_by_name(client: &Client, room: &str) -> Result<Joined, Error> {
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
                .await?;
            let matching: Vec<&matrix_sdk::room::Joined> = rooms
                .iter()
                .filter(|&joined_room| joined_room.room_id() == room_alias.room_id)
                .collect();
            match matching.len() {
                1 => matching[0].clone(),
                x if x > 1 => return Err(Error::MultipleRoomNameMatchesError(String::from(room))),
                _ => return Err(Error::NoSuchRoomError(String::from(room))),
            }
        }
    };
    Ok(room)
}
