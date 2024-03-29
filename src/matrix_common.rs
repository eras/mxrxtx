use crate::{config, matrix_log, progress_common};
use matrix_sdk::config::{RequestConfig, SyncSettings};
use matrix_sdk::ruma::api::client::{filter, sync::sync_events};
use matrix_sdk::ruma::OwnedDeviceId;
use matrix_sdk::sync::SyncResponse;
use matrix_sdk::{room::Joined, Client, LoopCtrl};
use std::convert::TryFrom;
use std::time::Duration;
use thiserror::Error;
use tokio::sync::mpsc;
use tracing::instrument;

#[allow(unused_imports)]
use log::{debug, error, info, warn};

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    MatrixSdkError(#[from] matrix_sdk::Error),

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

    #[error(transparent)]
    MatrixLogError(#[from] matrix_log::Error),
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
    rooms.iter().map(|x| format!("{x:?}")).collect()
}

#[instrument]
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

pub async fn sync_once_with_token(
    client: &Client,
    sync_settings: SyncSettings,
) -> Result<SyncResponse, Error> {
    let (send, mut receive) = mpsc::unbounded_channel();
    client
        .sync_with_result_callback(sync_settings, |response| async {
            send.send(response).unwrap();
            Ok(LoopCtrl::Break)
        })
        .await?;
    Ok(receive.recv().await.unwrap()?)
}

pub struct MatrixInit {
    pub client: Client,
    pub device_id: OwnedDeviceId,
    pub device_name: String,
    pub matrix_log: matrix_log::MatrixLog,
}

async fn get_device_name(client: &Client) -> Result<String, Error> {
    for device in client.devices().await?.devices {
        if Some(device.device_id) == client.device_id().map(|x| x.to_owned()) {
            if let Some(device_name) = device.display_name {
                return Ok(device_name);
            }
        }
    }
    Ok(client
        .device_id()
        .map(|x| x.to_string())
        .unwrap_or_else(|| "unknown".to_string()))
}

pub async fn init(config: &config::Config) -> Result<MatrixInit, Error> {
    let spinner = progress_common::make_spinner(None);
    spinner.set_message("Setup session");

    let session = config.get_matrix_session()?;

    let client = Client::builder();
    let client = if let Some(hs) = &config.homeserver {
        client.homeserver_url(hs)
    } else {
        client.server_name(session.user_id.server_name())
    };
    let client = client
        // account for slow homeservers..
        .request_config(RequestConfig::default().timeout(Duration::from_secs(120)))
        .sled_store(&config.state_dir, None)
        .build()
        .await?;
    let sync_settings = SyncSettings::default();
    let device_id = session.device_id.clone();
    spinner.set_message("Restore session");
    client.restore_session(session).await?;

    spinner.set_message("Sync");
    let _sync_response = sync_once_with_token(&client, sync_settings).await?;

    let device_name = get_device_name(&client).await?;
    let matrix_log = matrix_log::MatrixLog::new(&client, config, &device_name).await?;

    Ok(MatrixInit {
        client,
        device_id,
        device_name,
        matrix_log,
    })
}
