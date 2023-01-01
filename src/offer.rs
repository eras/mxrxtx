use crate::{config, matrix_common, matrix_signaling::MatrixSignaling, protocol, transport};
use futures::{AsyncReadExt, AsyncWriteExt};
use matrix_sdk::config::SyncSettings;
use matrix_sdk::Client;
use std::fs::{self, File};
use std::io::Read;
use std::path::{Path, PathBuf};
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

    #[error(transparent)]
    TransportError(#[from] transport::Error),

    #[error(transparent)]
    MatrixUriGenError(#[from] matrix_uri::MatrixUriGenError),

    #[error(transparent)]
    IoError(#[from] std::io::Error),
}

pub async fn transfer(
    files: Vec<PathBuf>,
    mut transport: transport::Transport,
) -> Result<(), Error> {
    println!("Accepting!");
    let mut cn = transport.accept().await?;
    println!("Accepted!");
    let mut buffer: [u8; 1024] = [0; 1024];
    for file in files {
        let mut file = File::open(file)?;
        let mut eof = false;
        while !eof {
            let n = file.read(&mut buffer)?;
            dbg!(n);
            if n > 0 {
                cn.write_all(&buffer[0..n]).await?;
            } else {
                eof = true;
            }
        }
    }
    println!("Waiting ack");
    cn.read_exact(&mut buffer[0..2]).await?;
    println!("Received ack, stopping");
    transport.stop().await?;
    println!("Stopped!");
    Ok(())
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
    let device_id = session.device_id.clone();
    client.restore_login(session).await?;

    let first_sync_response = client.sync_once(sync_settings.clone()).await?;

    let room = matrix_common::get_joined_room_by_name(&client, room).await?;
    println!("room: {:?}", room);

    let offer_files: Vec<protocol::File> = files
        .iter()
        .map(|file| {
            fs::metadata(Path::new(&file)).map(|metadata| protocol::File {
                name: file.to_string(),
                content_type: String::from("application/octet-stream"),
                size: metadata.len(), // TODO: respect this when sending file
            })
        })
        .try_fold(Vec::new(), |mut acc: Vec<protocol::File>, file_result| {
            acc.push(file_result?);
            Result::<_, Error>::Ok(acc)
        })?;

    let offer = protocol::OfferContent { files: offer_files };

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
    )?;

    println!(
        "Offer for {} started; press ctrl-c to redact",
        uri.matrix_uri_string()
    );
    let ctrl_c = tokio::signal::ctrl_c();

    let sync_settings = SyncSettings::default()
        .filter(filter)
        .timeout(Duration::from_millis(10000))
        .token(first_sync_response.next_batch);

    let signaling = MatrixSignaling::new(client.clone(), device_id, event_id.clone(), None).await;
    let transport = transport::Transport::new(signaling)?;

    let task = tokio::spawn({
        let files: Vec<PathBuf> = files
            .into_iter()
            .map(|file| Path::new(file).to_path_buf())
            .collect();
        async move { transfer(files, transport).await }
    });

    select! {
    	_done = ctrl_c => (),
    	done = client.sync(sync_settings) => {
	    done?;
	}
	_exit = task => (),
    }

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
