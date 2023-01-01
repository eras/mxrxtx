use crate::{
    config, level_event::LevelEvent, matrix_common, matrix_signaling::MatrixSignaling, protocol,
    transport::Transport,
};
use futures::{AsyncReadExt, AsyncWriteExt};
use matrix_sdk::config::SyncSettings;
use matrix_sdk::Client;
use std::convert::TryFrom;
use std::fs::{self, File};
use std::io::Read;
use std::path::Path;
use std::sync::Arc;
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

    let filter = matrix_common::just_joined_rooms_filter();
    let sync_settings = SyncSettings::default()
        .filter(filter.clone())
        .full_state(true);
    let client = Client::builder()
        .server_name(session.user_id.server_name())
        .sled_store(state_dir, None)?
        .build()
        .await?;
    client.restore_login(session).await?;

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
            match matching.len() {
                1 => matching[0].clone(),
                x if x > 1 => return Err(Error::MultipleRoomNameMatchesError(String::from(room))),
                _ => return Err(Error::NoSuchRoomError(String::from(room))),
            }
        }
    };
    println!("room: {:?}", room);

    let offer_files: Vec<protocol::File> = files
        .iter()
        .map(|file| protocol::File {
            name: file.to_string(),
            content_type: String::from("application/octet-stream"),
            size: fs::metadata(Path::new(&file)).unwrap().len(), // TODO: respect this when sending file
        })
        .collect();

    let offer = protocol::OfferContent { files: offer_files };

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
        .filter(filter)
        .timeout(Duration::from_millis(10000))
        .token(first_sync_response.next_batch);

    let exit_event = Arc::new(LevelEvent::new());
    let signaling = MatrixSignaling::new(client.clone(), None).await;
    let mut transport = Transport::new(signaling).unwrap();

    let task = tokio::spawn({
        let exit_event = exit_event.clone();
        let files: Vec<_> = files
            .into_iter()
            .map(|file| Path::new(file).to_path_buf())
            .collect();
        async move {
            println!("Accepting!");
            let mut cn = transport.accept().await.unwrap();
            println!("Accepted!");
            let mut buffer: [u8; 1024] = [0; 1024];
            for file in files {
                let mut file = File::open(file).unwrap();
                let mut eof = false;
                while !eof {
                    let n = file.read(&mut buffer).unwrap();
                    dbg!(n);
                    if n > 0 {
                        cn.write_all(&buffer[0..n]).await.unwrap();
                    } else {
                        eof = true;
                    }
                }
            }
            println!("Waiting ack");
            cn.read_exact(&mut buffer[0..2]).await.unwrap();
            println!("Received ack, stopping");
            transport.stop().await.unwrap();
            println!("Stopped!");
            exit_event.issue().await;
        }
    });

    select! {
    	_done = ctrl_c => (),
    	done = client.sync(sync_settings) => {
	    done?;
	}
	_exit = task => (),
    }
    exit_event.issue().await;

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
