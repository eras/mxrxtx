use crate::{config, matrix_common, protocol};
use matrix_sdk::uuid::Uuid;
use ruma_client_api::r0::{room::get_room_event, to_device::send_event_to_device};
use std::convert::TryFrom;
use std::str::FromStr;
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
}

#[derive(Error, Debug)]
pub struct MatrixUriParseError(matrix_uri::MatrixUriParseError);

impl std::fmt::Display for MatrixUriParseError {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        fmt.write_fmt(format_args!("Matrix URI parse error: {:?}", self.0))
    }
}

pub async fn download(config: config::Config, urls: Vec<&str>) -> Result<(), Error> {
    let session = config.get_matrix_session()?;
    let client = matrix_sdk::Client::new_from_user_id(session.user_id.clone()).await?;
    client.restore_login(session).await?;

    let uri = matrix_uri::MatrixUri::from_str(urls[0]).map_err(|x| MatrixUriParseError(x))?;
    let room_id = match uri.mxid.id_type {
        matrix_uri::IdType::RoomId => &uri.mxid.body,
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
                ruma_identifiers::EventId::try_from(child_mxid.body.clone())?
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
    let _rooms = matrix_common::get_joined_rooms(&client).await?;
    let room = client
        .get_joined_room(&ruma::RoomId::try_from(room_id.as_str())?)
        .ok_or(Error::NoSuchRoomError(String::from(room_id)))?;

    let event = room
        .event(get_room_event::Request::new(room.room_id(), &event_id))
        .await?;
    let user_id = match event.event.deserialize()? {
        ruma_events::AnyRoomEvent::Message(ruma_events::AnyMessageEvent::RoomMessage(
            message_event,
        )) => message_event.sender,
        _ => return Err(Error::NotAMessageEventError(event_id.as_str().to_string())),
    };

    println!("event: {:?}", event);

    let txn_id = Uuid::new_v4().to_string();
    let txn_id = txn_id.as_str();
    use ruma_common::to_device::DeviceIdOrAllDevices;
    use ruma_events::AnyToDeviceEventContent;
    use ruma_serde::Raw;
    use std::collections::BTreeMap;
    type Foo = BTreeMap<DeviceIdOrAllDevices, Raw<AnyToDeviceEventContent>>;
    let mut messages = send_event_to_device::Messages::new();
    let all = DeviceIdOrAllDevices::AllDevices;

    let establish_session = protocol::MxrxtxEvent::RequestSession(protocol::SessionInfo {
        event_id: event_id.clone(),
        webrtc_ice: String::from("moi"),
    });

    let establish_session_event: Raw<AnyToDeviceEventContent> =
        ruma_serde::Raw::from_json(serde_json::value::to_raw_value(&establish_session)?);

    let foos: Foo = vec![(all, establish_session_event)].into_iter().collect();

    messages.insert(user_id, foos);
    let x =
        send_event_to_device::Request::new_raw("fi.variaattori.mxrxtx.session", txn_id, messages);
    client.send(x, None).await?;

    Ok(())
}
