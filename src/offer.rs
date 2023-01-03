use crate::{
    config, level_event::LevelEvent, matrix_common, matrix_signaling::MatrixSignalingRouter,
    protocol, signaling::SignalingRouter, transport,
};
use futures::{future::BoxFuture, AsyncReadExt, AsyncWriteExt};
use matrix_sdk::config::SyncSettings;
use matrix_sdk::Client;
use std::fs::{self, File};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::time::Duration;
use thiserror::Error;
use tokio::select;

#[allow(unused_imports)]
use log::{debug, error, info, warn};

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    ConfigError(#[from] config::Error),

    #[error(transparent)]
    RumaError(#[from] matrix_sdk::Error),

    #[error(transparent)]
    MatrixHttpError(#[from] matrix_sdk::HttpError),

    #[error(transparent)]
    MatrixCommonError(#[from] matrix_common::Error),

    #[error(transparent)]
    MatrixClientbuildError(#[from] matrix_sdk::ClientBuildError),

    #[error(transparent)]
    OpenStoreError(#[from] matrix_sdk_sled::OpenStoreError),

    #[error(transparent)]
    TransportError(#[from] transport::Error),

    #[error(transparent)]
    MatrixUriGenError(#[from] matrix_uri::MatrixUriGenError),

    #[error(transparent)]
    IoError(#[from] std::io::Error),
}

pub async fn transfer(files: Vec<PathBuf>, mut cn: transport::DataStream) -> Result<(), Error> {
    let mut buffer: [u8; 1024] = [0; 1024];
    for file in files {
        let mut file = File::open(file)?;
        let mut eof = false;
        while !eof {
            let n = file.read(&mut buffer)?;
            if n > 0 {
                cn.write_all(&buffer[0..n]).await?;
            } else {
                eof = true;
            }
        }
    }
    debug!("Waiting ack");
    cn.read_exact(&mut buffer[0..2]).await?;
    Ok(())
}

// https://github.com/rust-lang/rust/issues/78649#issuecomment-1264353351
pub fn accepter_recurse(
    exit_signal: LevelEvent,
    files: Vec<PathBuf>,
    signaling_router: MatrixSignalingRouter,
) -> BoxFuture<'static, ()> {
    Box::pin(async move {
        accepter(exit_signal, files, signaling_router)
            .await
            .unwrap()
    }) as BoxFuture<()>
}

pub async fn accepter(
    exit_signal: LevelEvent,
    files: Vec<PathBuf>,
    mut signaling_router: MatrixSignalingRouter,
) -> Result<(), Error> {
    info!("Waiting for new signaling peer");
    let signaling = signaling_router.accept().await.unwrap();
    tokio::spawn({
        let exit_signal = exit_signal.clone();
        let files = files.clone();
        async move { accepter_recurse(exit_signal, files, signaling_router).await }
    });
    let mut transport = transport::Transport::new(signaling)?;
    debug!("Accepting!");
    let cn = transport.accept().await?;
    transfer(files, cn).await?;
    debug!("Accepted!");
    // debug!("Received ack, stopping");
    // transport.stop().await?;
    // info!("Transfer stopped");

    Ok(())
}

#[rustfmt::skip::macros(select)]
pub async fn offer(config: config::Config, room: &str, files: Vec<&str>) -> Result<(), Error> {
    let session = config.get_matrix_session()?;

    let filter = matrix_common::just_joined_rooms_filter();
    let sync_settings = SyncSettings::default()
        .filter(filter.clone())
        .full_state(true);
    let client = Client::builder()
        .server_name(session.user_id.server_name())
        .sled_store(config.state_dir, None)
        .build()
        .await?;
    let device_id = session.device_id.clone();
    client.restore_session(session).await?;

    let first_sync_response = client.sync_once(sync_settings.clone()).await?;

    let room = matrix_common::get_joined_room_by_name(&client, room).await?;
    debug!("room: {:?}", room);

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
        .send(offer, Some(&matrix_sdk::ruma::TransactionId::new()))
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
    let exit_signal = LevelEvent::new();
    tokio::spawn({
        let exit_signal = exit_signal.clone();
        async move {
            tokio::signal::ctrl_c()
                .await
                .expect("Failed to listen for ctrl-c");
            exit_signal.issue().await;
        }
    });

    let sync_settings = SyncSettings::default()
        .filter(filter)
        .timeout(Duration::from_millis(10000))
        .token(first_sync_response.next_batch);

    let signaling_router =
        MatrixSignalingRouter::new(client.clone(), device_id, event_id.clone()).await;

    tokio::spawn({
        let files: Vec<PathBuf> = files
            .into_iter()
            .map(|file| Path::new(file).to_path_buf())
            .collect();
        let exit_signal = exit_signal.clone();
        async move { accepter(exit_signal, files, signaling_router).await }
    });

    select! {
    	_exit = exit_signal.wait() => (),
    	done = client.sync(sync_settings) => {
	    done?;
	}
    }

    info!("Redacting offer");
    room.redact(
        &event_id,
        Some("Offer expired"),
        Some(matrix_sdk::ruma::TransactionId::new()),
    )
    .await?;
    debug!("Done");

    Ok(())
}
