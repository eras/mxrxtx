use crate::config;
use matrix_sdk::config::SyncSettings;
use matrix_sdk::ruma::api::client::{filter, sync::sync_events};
use matrix_sdk::ruma::OwnedDeviceId;
use matrix_sdk::sync::SyncResponse;
use matrix_sdk::{room::Joined, Client};
use std::convert::TryFrom;
use thiserror::Error;

#[allow(unused_imports)]
use log::{debug, error, info, warn};

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    RumaError(#[from] matrix_sdk::Error),

    #[error(transparent)]
    MatrixHttpError(#[from] matrix_sdk::HttpError),

    #[error("Matrix room not found: {}", .0)]
    NoSuchRoomError(String),

    #[error("Multiple matrix rooms matching pattern found matching {}: {:?}", .0, .1)]
    MultipleRoomNameMatchesError(String, Vec<String>),

    #[error("Room id/name must start with either ! or #: {}", .0)]
    RoomNameError(String),

    #[error(transparent)]
    IdParseError(#[from] matrix_sdk::ruma::IdParseError),

    #[error(transparent)]
    MatrixClientbuildError(#[from] matrix_sdk::ClientBuildError),

    #[error(transparent)]
    OpenStoreError(#[from] matrix_sdk_sled::OpenStoreError),

    #[error(transparent)]
    ConfigError(#[from] config::Error),
}

enum RoomType {
    RoomId,
    RoomAlias,
}

impl RoomType {
    fn classify(name: &str) -> Result<RoomType, Error> {
        let ch0 = name.chars().next();
        if ch0 == Some('!') {
            Ok(RoomType::RoomId)
        } else if ch0 == Some('#') {
            Ok(RoomType::RoomAlias)
        } else {
            Err(Error::RoomNameError(name.to_string()))
        }
    }
}

pub(crate) fn just_joined_rooms_filter() -> sync_events::v3::Filter {
    let mut empty_room_event_filter = filter::RoomEventFilter::empty();
    empty_room_event_filter.limit = Some(From::from(1u32));
    empty_room_event_filter.rooms = Some(vec![]);
    empty_room_event_filter.lazy_load_options = filter::LazyLoadOptions::Enabled {
        include_redundant_members: false,
    };

    let mut no_types_filter = filter::Filter::empty();
    no_types_filter.types = Some(vec![]);

    let mut filter_def = filter::FilterDefinition::empty();
    filter_def.presence = no_types_filter.clone();
    filter_def.account_data = no_types_filter;
    filter_def.room.include_leave = false;
    filter_def.room.account_data = empty_room_event_filter.clone();
    filter_def.room.timeline = empty_room_event_filter.clone();
    filter_def.room.ephemeral = empty_room_event_filter.clone();
    filter_def.room.state = empty_room_event_filter;
    sync_events::v3::Filter::FilterDefinition(filter_def)
}

fn room_strings(rooms: &[&Joined]) -> Vec<String> {
    rooms.iter().map(|x| format!("{:?}", x)).collect()
}

pub(crate) async fn get_joined_room_by_name(client: &Client, room: &str) -> Result<Joined, Error> {
    let room = match RoomType::classify(room) {
        Ok(RoomType::RoomId) => {
            let room_id = <&matrix_sdk::ruma::RoomId>::try_from(room)?.to_owned();
            client
                .get_joined_room(&room_id)
                .ok_or(Error::NoSuchRoomError(String::from(room)))?
        }
        Ok(RoomType::RoomAlias) => {
            let rooms = client.joined_rooms();
            let room_alias = client
                .resolve_room_alias(&matrix_sdk::ruma::RoomAliasId::parse(room)?)
                .await?;
            let matching: Vec<&matrix_sdk::room::Joined> = rooms
                .iter()
                .filter(|&joined_room| joined_room.room_id() == room_alias.room_id)
                .collect();
            match &matching[..] {
                [room] => (*room).clone(),
                rooms @ [_, _, ..] => {
                    return Err(Error::MultipleRoomNameMatchesError(
                        String::from(room),
                        room_strings(rooms),
                    ))
                }
                [] => return Err(Error::NoSuchRoomError(String::from(room))),
            }
        }
        Err(err @ Error::RoomNameError(_)) => {
            // match by room name
            if room.is_empty() {
                return Err(err);
            } else {
                let room_name = room.to_string();
                let room_name_lc = room_name.to_lowercase();
                let joined = client.joined_rooms();
                // First try to match in a non-case-sensitive manner
                let matching_rooms_nocase: Vec<_> = joined
                    .iter()
                    .filter(|joined_room| {
                        joined_room.name().map(|x| x.to_lowercase()).as_ref() == Some(&room_name_lc)
                    })
                    .cloned()
                    .collect();
                match &matching_rooms_nocase[..] {
                    [] => return Err(Error::NoSuchRoomError(room_name)),
                    [room] => room.clone(),
                    [_, _, ..] => {
                        // Next try only exact matches
                        let matching_rooms_case: Vec<_> = joined
                            .iter()
                            .filter(|joined_room| joined_room.name().as_ref() == Some(&room_name))
                            .cloned()
                            .collect();
                        match &matching_rooms_case[..] {
                            [] => return Err(Error::NoSuchRoomError(room_name)),
                            rooms @ [_, _, ..] => {
                                return Err(Error::MultipleRoomNameMatchesError(
                                    room_name,
                                    // lol
                                    room_strings(rooms.iter().collect::<Vec<_>>().as_slice()),
                                ));
                            }
                            [room] => room.clone(),
                        }
                    }
                }
            }
        }
        Err(err) => {
            return Err(err);
        }
    };
    Ok(room)
}

pub async fn init(config: &config::Config) -> Result<(Client, OwnedDeviceId, SyncResponse), Error> {
    let session = config.get_matrix_session()?;

    let sync_settings = SyncSettings::default()
        // .filter(just_joined_rooms_filter())
        // .full_state(true);
;
    let client = Client::builder()
        .server_name(session.user_id.server_name())
        .sled_store(&config.state_dir, None)
        .build()
        .await?;
    let device_id = session.device_id.clone();
    info!("Logging in");
    client.restore_session(session).await?;

    info!("Sync");
    let sync_response = client.sync_once(sync_settings).await?;

    Ok((client, device_id, sync_response))
}
