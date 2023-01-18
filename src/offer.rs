use crate::{
    config, digest, level_event::LevelEvent, matrix_common, matrix_log,
    matrix_signaling::MatrixSignalingRouter, progress_common, protocol, signaling::SignalingRouter,
    transport, utils::escape,
};
use futures::{future::BoxFuture, AsyncReadExt, AsyncWriteExt};
use indicatif::{MultiProgress, ProgressBar, ProgressFinish};
use matrix_sdk::config::SyncSettings;
use sha2::{Digest, Sha512};
use std::cmp;
use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::Read;
use std::path::Path;
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

    #[error(transparent)]
    MatrixLogError(#[from] matrix_log::Error),
}

pub fn make_transfer_progress(
    offer_files: &Vec<protocol::File>,
    multi: Option<&MultiProgress>,
) -> ProgressBar {
    let mut size = 0u64;
    for offer_file in offer_files {
        size += offer_file.size;
    }
    progress_common::make_transfer_progress(size, multi)
}

pub async fn transfer(
    offer_files: Vec<protocol::File>,
    mut cn: transport::DataStream,
    progress: ProgressBar,
) -> Result<(), Error> {
    let mut buffer: [u8; 1024] = [0; 1024];
    let mut total_bytes = 0;
    for offer_file in offer_files {
        let mut file = File::open(Path::new(&offer_file.name))?;
        let mut eof = false;
        let file_size = offer_file.size as usize;
        let mut sent_file_bytes = 0usize;
        let mut hasher = Sha512::new();
        while !eof && sent_file_bytes < file_size {
            let read_bytes = cmp::min(file_size - sent_file_bytes, buffer.len());
            let n = file.read(&mut buffer[0..read_bytes])?;
            progress.inc(n as u64);
            if n == 0 {
                eof = true;
            } else {
                cn.write_all(&buffer[0..n]).await?;
                hasher.update(&buffer[0..n]);
                total_bytes += n;
                sent_file_bytes += n;
            }
        }
        if sent_file_bytes < file_size {
            error!(
                "File {file} finished prematurely, aborting transfer",
                file = escape(&offer_file.name)
            );
            break;
        }
        if let Some(hash) = offer_file.hashes.get("sha512") {
            if hasher.finalize().to_vec() != hash.as_bytes() {
                error!(
                    "File {file} was changed during transfer (hash changed), aborting",
                    file = escape(&offer_file.name)
                );
                break;
            }
        }
    }
    debug!("Wrote {total_bytes}, waiting ack");
    progress.set_message("Waiting ACK");
    cn.read_exact(&mut buffer[0..2]).await?;
    Ok(())
}

// https://github.com/rust-lang/rust/issues/78649#issuecomment-1264353351
pub fn accepter_recurse(
    exit_signal: LevelEvent,
    offer_files: Vec<protocol::File>,
    signaling_router: MatrixSignalingRouter,
    ice_servers: Vec<String>,
    matrix_log: matrix_log::MatrixLog,
    multi_progress: MultiProgress,
) -> BoxFuture<'static, ()> {
    Box::pin(async move {
        accepter(
            exit_signal,
            offer_files,
            signaling_router,
            ice_servers.clone(),
            matrix_log,
            multi_progress,
        )
        .await
        // TODO: handle IO error when peer closes connection
        .unwrap()
    }) as BoxFuture<()>
}

pub async fn accepter(
    exit_signal: LevelEvent,
    offer_files: Vec<protocol::File>,
    mut signaling_router: MatrixSignalingRouter,
    ice_servers: Vec<String>,
    matrix_log: matrix_log::MatrixLog,
    multi_progress: MultiProgress,
) -> Result<(), Error> {
    let spinner =
        progress_common::make_spinner(Some(&multi_progress)).with_finish(ProgressFinish::AndClear);
    matrix_log
        .log(Some(&spinner), "Waiting for new signaling peer")
        .await?;
    let signaling = signaling_router.accept().await.unwrap();
    tokio::spawn({
        let ice_servers = ice_servers.clone();
        let exit_signal = exit_signal.clone();
        let offer_files = offer_files.clone();
        let matrix_log = matrix_log.clone();
        let multi_progress = multi_progress.clone();
        async move {
            accepter_recurse(
                exit_signal,
                offer_files,
                signaling_router,
                ice_servers,
                matrix_log,
                multi_progress,
            )
            .await
        }
    });
    let mut transport =
        transport::Transport::new(signaling, ice_servers.iter().map(|x| x.as_str()).collect())?;
    matrix_log
        .log(Some(&spinner), "Accepting a connection")
        .await?;
    let cn = transport.accept().await?;
    matrix_log
        .log(Some(&spinner), "Accepted a connection, transferring file")
        .await?;
    let progress = make_transfer_progress(&offer_files, Some(&multi_progress));
    transfer(offer_files, cn, progress).await?;
    matrix_log.log(None, "Transferring complete").await?;
    // debug!("Received ack, stopping");
    // transport.stop().await?;
    // info!("Transfer stopped");

    Ok(())
}

#[rustfmt::skip::macros(select)]
pub async fn offer(
    config: config::Config,
    room: &str,
    offer_files: Vec<&str>,
) -> Result<(), Error> {
    let matrix_common::MatrixInit {
        client,
        device_id,
        matrix_log,
        ..
    } = matrix_common::init(&config).await?;

    let multi_progress = MultiProgress::new();
    let spinner = progress_common::make_spinner(Some(&multi_progress));
    matrix_log.log(Some(&spinner), "Starting").await?;

    let room = matrix_common::get_joined_room_by_name(&client, room).await?;
    debug!("room: {:?}", room);

    let offer_files: Vec<protocol::File> = offer_files
        .iter()
        .map(|file| {
            let (sha512, size) = digest::file_sha512(Path::new(&file));
            let mut hashes = BTreeMap::new();
            hashes.insert("sha512".to_string(), sha512);
            debug!("moi");
            fs::metadata(Path::new(&file)).map(|_metadata| protocol::File {
                // we need to get date later so let's not drop this metadata thing yet..
                name: file.to_string(),
                mimetype: String::from("application/octet-stream"),
                size, // TODO: respect this when sending file
                thumbnail_file: None,
                thumbnail_info: None,
                thumbnail_url: None,
                hashes,
            })
        })
        .try_fold(Vec::new(), |mut acc: Vec<protocol::File>, file_result| {
            acc.push(file_result?);
            Result::<_, Error>::Ok(acc)
        })?;

    let offer = protocol::OfferContent {
        name: None,
        description: None,
        files: offer_files.clone(),
        thumbnail_info: None,
        thumbnail_url: None,
    };

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

    matrix_log
        .log(
            Some(&spinner),
            &format!("Offer for {} started", escape(&uri.matrix_uri_string())),
        )
        .await?;

    let sync_settings = SyncSettings::default().filter(matrix_common::just_joined_rooms_filter());

    let signaling_router =
        MatrixSignalingRouter::new(client.clone(), device_id, event_id.clone()).await;

    tokio::spawn({
        let exit_signal = exit_signal.clone();
        let matrix_log = matrix_log.clone();
        let multi_progress = multi_progress.clone();
        async move {
            accepter(
                exit_signal,
                offer_files,
                signaling_router,
                config.ice_servers,
                matrix_log,
                multi_progress,
            )
            .await
        }
    });

    select! {
    	_exit = exit_signal.wait() => (),
    	done = client.sync(sync_settings) => {
	    done?;
	}
    }

    room.redact(
        &event_id,
        None,
        Some(matrix_sdk::ruma::TransactionId::new()),
    )
    .await?;
    matrix_log.log(None, "Offer stopped (redacted)").await?;
    spinner.finish_with_message("Offer stopped (redacted)");

    Ok(())
}
