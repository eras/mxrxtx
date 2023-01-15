use crate::{
    config, level_event::LevelEvent, matrix_common, matrix_signaling::MatrixSignalingRouter,
    protocol, signaling::SignalingRouter, transport, utils::escape,
};
use futures::{future::BoxFuture, AsyncReadExt, AsyncWriteExt};
use matrix_sdk::config::SyncSettings;
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
    MatrixSdkError(#[from] matrix_sdk::Error),

    #[error(transparent)]
    MatrixHttpError(#[from] matrix_sdk::HttpError),

    #[error(transparent)]
    MatrixCommonError(#[from] matrix_common::Error),

    #[error(transparent)]
    TransportError(#[from] transport::Error),

    #[error(transparent)]
    MatrixUriGenError(#[from] matrix_uri::MatrixUriGenError),

    #[error(transparent)]
    IoError(#[from] std::io::Error),
}

pub async fn transfer(files: Vec<PathBuf>, mut cn: transport::DataStream) -> Result<(), Error> {
    let mut buffer: [u8; 1024] = [0; 1024];
    let mut total_bytes = 0;
    for file in files {
        let mut file = File::open(file)?;
        let mut eof = false;
        while !eof {
            let n = file.read(&mut buffer)?;
            if n > 0 {
                cn.write_all(&buffer[0..n]).await?;
                total_bytes += n;
            } else {
                eof = true;
            }
        }
    }
    debug!("Wrote {total_bytes}, waiting ack");
    cn.read_exact(&mut buffer[0..2]).await?;
    Ok(())
}

// https://github.com/rust-lang/rust/issues/78649#issuecomment-1264353351
pub fn accepter_recurse(
    exit_signal: LevelEvent,
    files: Vec<PathBuf>,
    signaling_router: MatrixSignalingRouter,
    ice_servers: Vec<String>,
) -> BoxFuture<'static, ()> {
    Box::pin(async move {
        accepter(exit_signal, files, signaling_router, ice_servers.clone())
            .await
            .unwrap()
    }) as BoxFuture<()>
}

pub async fn accepter(
    exit_signal: LevelEvent,
    files: Vec<PathBuf>,
    mut signaling_router: MatrixSignalingRouter,
    ice_servers: Vec<String>,
) -> Result<(), Error> {
    info!("Waiting for new signaling peer");
    let signaling = signaling_router.accept().await.unwrap();
    tokio::spawn({
        let ice_servers = ice_servers.clone();
        let exit_signal = exit_signal.clone();
        let files = files.clone();
        async move { accepter_recurse(exit_signal, files, signaling_router, ice_servers).await }
    });
    let mut transport =
        transport::Transport::new(signaling, ice_servers.iter().map(|x| x.as_str()).collect())?;
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
    let (client, device_id, first_sync_response) = matrix_common::init(&config).await?;

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
        escape(&uri.matrix_uri_string())
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
        .filter(matrix_common::just_joined_rooms_filter())
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
        async move { accepter(exit_signal, files, signaling_router, config.ice_servers).await }
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
