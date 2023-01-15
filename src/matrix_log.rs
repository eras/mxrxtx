use crate::{config, matrix_common, utils};
use matrix_sdk::ruma::events::room::message::RoomMessageEventContent;
use matrix_sdk::{room::Joined, Client};
use thiserror::Error;

#[allow(unused_imports)]
use log::{debug, error, info, warn};

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    MatrixCommonError(#[from] Box<matrix_common::Error>),

    #[error(transparent)]
    MatrixSdkError(#[from] matrix_sdk::Error),
}

#[derive(Clone)]
pub struct MatrixLog {
    log_room: Option<Joined>,
    device_str: String,
}

impl MatrixLog {
    pub async fn new(client: &Client, config: &config::Config) -> Result<Self, Error> {
        match &config.log_room {
            None => Ok(MatrixLog {
                log_room: None,
                device_str: "".to_string(),
            }),
            Some(log_room) => {
                let log_room = matrix_common::get_joined_room_by_name(client, log_room)
                    .await
                    .map_err(Box::new)?;
                let log_room = Some(log_room);
                let device_id = match client.device_id() {
                    Some(device_id) => utils::escape(device_id.as_ref()),
                    None => "unknown".to_string(),
                };
                Ok(MatrixLog {
                    log_room,
                    device_str: device_id,
                })
            }
        }
    }

    pub async fn log(&self, message: &str) -> Result<(), Error> {
        info!("{message}");
        match &self.log_room {
            None => Ok(()),
            Some(log_room) => {
                let content = RoomMessageEventContent::notice_plain(format!(
                    "mxrxtx {device_id}> {message}",
                    device_id = self.device_str
                ));
                log_room.send(content, None).await?;
                Ok(())
            }
        }
    }
}
