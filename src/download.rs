use crate::{config, matrix_common};
use ruma_client_api::r0::room::get_room_event;
use thiserror::Error;
use std::str::FromStr;
use std::convert::TryFrom;

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
    MatrixUriIsNotRoomId(String),

    #[error("Matrix uri does not have event id: {}", .0)]
    MatrixUriMissingEventId(String),

    #[error(transparent)]
    MatrixHttpError(#[from] matrix_sdk::HttpError),

    #[error(transparent)]
    MatrixCommonError(#[from] matrix_common::Error),

    #[error("Matrix room not found: {}", .0)]
    NoSuchRoomError(String),
}

#[derive(Error, Debug)]
pub struct MatrixUriParseError(matrix_uri::MatrixUriParseError);

impl std::fmt::Display for MatrixUriParseError {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
	fmt.write_fmt(format_args!("Matrix URI parse error: {:?}", self.0))
    }
}

pub async fn download(config: config::Config,
		      urls: Vec<&str>) -> Result<(), Error> {
    let session = config.get_matrix_session()?;
    let client = matrix_sdk::Client::new_from_user_id(session.user_id.clone()).await?;
    client.restore_login(session).await?;

    let uri = matrix_uri::MatrixUri::from_str(urls[0]).map_err(|x| MatrixUriParseError(x))?;
    let room_id =
	match uri.mxid.id_type {
	    matrix_uri::IdType::RoomId => &uri.mxid.body,
	    _ => return Err(Error::MatrixUriIsNotRoomId(format!("{:?}", uri.mxid.id_type))),
	};
    let event_id =
	match uri.child_mxid {
	    Some(child_mxid) =>
		match child_mxid.id_type {
		    matrix_uri::IdType::EventId => ruma_identifiers::EventId::try_from(child_mxid.body.clone())?,
		    _ => return Err(Error::MatrixUriMissingEventId(format!("{:?}", child_mxid.id_type))),
		}
	    _ => return Err(Error::MatrixUriMissingEventId(format!("{:?}", uri.mxid.id_type))),
	};

    // needed to populate Client internal data
    let _rooms = matrix_common::get_joined_rooms(&client).await?;
    let room = client.get_joined_room(&ruma::RoomId::try_from(room_id.as_str())?)
	.ok_or(Error::NoSuchRoomError(String::from(room_id)))?;

    let event = room.event(get_room_event::Request::new(room.room_id(), &event_id)).await?;

    println!("event: {:?}", event);

    Ok(())
}
