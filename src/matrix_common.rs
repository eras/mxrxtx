use ruma::api::client::r0::{filter, sync::sync_events};
use std::time::Duration;
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
}

pub(crate) async fn get_joined_rooms(
    client: &matrix_sdk::Client,
) -> Result<Vec<matrix_sdk::room::Joined>, Error> {
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
    let sync_settings = matrix_sdk::SyncSettings::default()
        .filter(sync_events::Filter::FilterDefinition(filter_def))
        .timeout(Duration::from_millis(1000))
        .full_state(true);
    let _sync_response = client.sync_once(sync_settings).await?;
    Ok(client.joined_rooms())
}
