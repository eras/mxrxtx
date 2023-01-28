use crate::{
    config, digest,
    matrix_common, matrix_log,
    matrix_signaling::{MatrixSignalingRouter, MatrixSignalingSingle},
    progress_common, protocol,
    signaling::Signaling,
    signaling::SignalingRouter,
    transfer_session::TransferSession,
    transport,
    utils::escape,
    version::get_version,
};
use futures::{AsyncReadExt, AsyncWriteExt};
use indicatif::{MultiProgress, ProgressBar, ProgressFinish};
use matrix_sdk::config::SyncSettings;
use sha2::{Digest, Sha512};
use std::cmp;
use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::Read;
use std::path::Path;
use std::sync::Arc;
use thiserror::Error;
use tokio::select;
use tokio::sync::mpsc;
use tokio::sync::Mutex;
use tokio_util::sync::CancellationToken;
use tracing::{event, Level, instrument};

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
    DigestError(#[from] digest::Error),

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

#[rustfmt::skip::macros(select)]
#[instrument(skip_all)]
pub async fn transfer(
    offer_files: Vec<protocol::File>,
    mut cn: transport::DataStream,
    progress: ProgressBar,
    cancel: CancellationToken,
) -> Result<(), Error> {
    let mut abort = false;
    let mut buffer: [u8; 1024] = [0; 1024];
    let mut total_bytes = 0;
    event!(Level::TRACE, is_cancelled=cancel.is_cancelled());
    for offer_file in offer_files {
        let mut file = File::open(Path::new(&offer_file.name))?;
        let mut eof = false;
        let file_size = offer_file.size as usize;
        let mut sent_file_bytes = 0usize;
        let mut hasher = Sha512::new();
        while !eof && sent_file_bytes < file_size && !cancel.is_cancelled() {
            let read_bytes = cmp::min(file_size - sent_file_bytes, buffer.len());
            let n = file.read(&mut buffer[0..read_bytes])?;
            progress.inc(n as u64);
            if n == 0 {
                eof = true;
            } else {
		select! {
		    _ = cancel.cancelled() => {
			event!(Level::TRACE, "Cancelled");
		    },
		    result = cn.write_all(&buffer[0..n]) => {
			result?;
			hasher.update(&buffer[0..n]);
			total_bytes += n;
			sent_file_bytes += n;
		    }
		}
            }
        }
	if cancel.is_cancelled() {
	    abort = true;
	} else {
            if sent_file_bytes < file_size {
		abort = true;
		error!(
                    "File {file} finished prematurely, aborting transfer",
                    file = escape(&offer_file.name)
		);
		break;
            }
            if let Some(hash) = offer_file.hashes.get("sha512") {
		if hasher.finalize().to_vec() != hash.as_bytes() {
		    abort = true;
                    error!(
			"File {file} was changed during transfer (hash changed), aborting",
			file = escape(&offer_file.name)
                    );
                    break;
		}
            }
	}
    }
    if !abort {
	debug!("Wrote {total_bytes}, waiting ack");
	progress.set_message("Waiting ACK");
	cn.read_exact(&mut buffer[0..2]).await?;
    } else {
	debug!("Transfer aborted");
    }
    event!(Level::TRACE, is_cancelled=cancel.is_cancelled());
    Ok(())
}

#[derive(Clone)]
struct AccepterState {
    offer_files: Vec<protocol::File>,
    ice_servers: Vec<String>,
    matrix_log: matrix_log::MatrixLog,
    multi_progress: MultiProgress,
    offer_session_state: Arc<Mutex<TransferSession>>,
    max_transfers: Option<usize>,
    cancel: CancellationToken,
}

// ⛼ Removed here code for doing recursion with async functions, as per https://github.com/rust-lang/rust/issues/78649#issuecomment-1264353351

#[instrument(skip_all)]
async fn handle_accept(
    signaling: MatrixSignalingSingle,
    mut accepter_state: AccepterState,
    spinner: ProgressBar,
) -> Result<(), Error> {
    let AccepterState {
        matrix_log,
        multi_progress,
        ice_servers,
        offer_files,
        offer_session_state,
        max_transfers,
        cancel,
    } = &mut accepter_state;
    let peer_info = signaling.get_peer_info().await;
    let mut transport =
        transport::Transport::new(signaling, ice_servers.iter().map(|x| x.as_str()).collect())?;
    let peer = peer_info
        .mxid
        .map(|x| escape(x.as_ref()))
        .unwrap_or_else(|| String::from("Unknown"));
    matrix_log
        .log(
            Some(&spinner),
            &format!("Accepting a connection from {peer}"),
        )
        .await?;
    let cn = transport.accept().await?;
    matrix_log
        .log(
            Some(&spinner),
            &format!("Accepted a connection, transferring file to {peer}"),
        )
        .await?;
    let progress = make_transfer_progress(offer_files, Some(multi_progress));
    offer_session_state.lock().await.inc_tranferring();
    progress.set_prefix(format!("{peer} "));
    let transfer_task = tokio::spawn({
	let cancel = cancel.clone();
	let offer_files = offer_files.clone();
	async move {
	    transfer(offer_files.to_vec(), cn, progress, cancel).await
	}}
    );
    let result =
	select! {
            _exit = cancel.cancelled() => None,
            result = transfer_task => {
		event!(Level::TRACE, is_cancelled=cancel.is_cancelled());
		Some(result.unwrap()) // TODO: error handling?
	    }
	};
    if let Some(result) = result {
	result?;
    }
    matrix_log
        .log(None, &format!("Transferring complete to {peer}"))
        .await?;
    // debug!("Received ack, stopping");
    // transport.stop().await?;
    // info!("Transfer stopped");

    let num_transfers = offer_session_state.lock().await.inc_complete();
    if let Some(max_transfers) = *max_transfers {
        if num_transfers >= max_transfers {
            matrix_log
                .log(None, "All transfers used up, stopping")
                .await?;
            cancel.cancel();
        }
    }
    event!(Level::TRACE, is_cancelled=cancel.is_cancelled());
    Ok(())
}

#[rustfmt::skip::macros(select)]
async fn accepter(
    accepter_state: AccepterState,
    mut signaling_router: MatrixSignalingRouter,
) -> Result<(), Error> {
    let (finished_send, mut finished_recv) = mpsc::unbounded_channel();
    let matrix_log = &accepter_state.matrix_log;
    let multi_progress = &accepter_state.multi_progress;
    let top_spinner = progress_common::make_spinner(Some(multi_progress))
	.with_finish(ProgressFinish::AndClear);
    matrix_log
        .log(Some(&top_spinner), "Waiting for new signaling peer")
        .await?;
    loop {
	let signaling = select! {
	    _done = accepter_state.cancel.cancelled() => {
		break;
	    }
	    retvalue = finished_recv.recv() => {
		match retvalue {
		    Some(Ok(_)) => {
			// everything went great!
			None
		    }
		    None => {
			// what? exit.
			error!("Unexpected closing of finished_recv");
			break;
		    }
		    Some(Err(error)) => {
			matrix_log
			    .log(None, &format!("Error from accepter: {error:?}"))
			    .await?;
			None
		    }
		}
	    }
	    signaling = signaling_router.accept() => {
		match signaling {
		    Ok(signaling) => {
			Some(signaling)
		    }
		    Err(error) => {
			matrix_log
			    .log(None, &format!("Error from signaling: {error:?}"))
			    .await?;
			None
		    }
		}
	    }
	};

	if let Some(signaling) = signaling {
            tokio::spawn({
		let spinner = progress_common::make_spinner(Some(multi_progress))
		    .with_finish(ProgressFinish::AndClear);
		let accepter_state = accepter_state.clone();
		let finished_send = finished_send.clone();
		async move {
                    let result = handle_accept(signaling, accepter_state, spinner).await;
                    let _ignore_error = finished_send.send(result);
		}
            });
	}
    }
    event!(Level::TRACE, is_cancelled=accepter_state.cancel.is_cancelled());

    Ok(())
}

#[rustfmt::skip::macros(select)]
#[instrument(skip_all)]
pub async fn offer(
    config: config::Config,
    room: &str,
    offer_files: Vec<&str>,
    max_transfers: Option<usize>,
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

    matrix_log
        .log(Some(&spinner), "Calculating checksums")
        .await?;
    let offer_files: Vec<protocol::File> = offer_files
        .iter()
        .map(|file| -> Result<protocol::File, Error> {
            let (sha512, size) = digest::file_sha512(Path::new(&file), Some(&multi_progress))?;
            let mut hashes = BTreeMap::new();
            hashes.insert("sha512".to_string(), sha512);
            Ok(
                fs::metadata(Path::new(&file)).map(|_metadata| protocol::File {
                    // we need to get date later so let's not drop this metadata thing yet..
                    name: file.to_string(),
                    mimetype: String::from("application/octet-stream"),
                    size, // TODO: respect this when sending file
                    thumbnail_file: None,
                    thumbnail_info: None,
                    thumbnail_url: None,
                    hashes,
                })?,
            )
        })
        .try_fold(Vec::new(), |mut acc: Vec<protocol::File>, file_result| {
            acc.push(file_result?);
            Result::<_, Error>::Ok(acc)
        })?;

    let offer = protocol::OfferContent {
        version: get_version(),
        name: None,
        description: None,
        files: offer_files.clone(),
        thumbnail_info: None,
        thumbnail_url: None,
    };

    matrix_log.log(Some(&spinner), "Sending event").await?;

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

    let master_cancel = CancellationToken::new();
    let cancel = master_cancel.clone();
    tokio::spawn({
        let matrix_log = matrix_log.clone();
	let spinner = spinner.clone();
        async move {
	    let _cancel_guard = master_cancel.drop_guard();
            tokio::signal::ctrl_c()
                .await
                .expect("Failed to listen for ctrl-c");
	    let _ignore = matrix_log
		.log(
                    Some(&spinner),
                    "Stopping due to SIGINT",
		)
		.await;
        }
    });

    let sync_settings = SyncSettings::default().filter(matrix_common::just_joined_rooms_filter());

    let signaling_router =
        MatrixSignalingRouter::new(client.clone(), device_id, event_id.clone()).await;

    tokio::spawn({
        let matrix_log = matrix_log.clone();
        let multi_progress = multi_progress.clone();
        matrix_log
            .log(
                Some(&spinner),
                &format!("Offering {}", &uri.matrix_uri_string()),
            )
            .await?;
        let offer_session_state = Arc::new(Mutex::new(TransferSession::new(&multi_progress)));
        let accepter_state = AccepterState {
            offer_files,
            ice_servers: config.ice_servers,
            matrix_log,
            multi_progress,
            offer_session_state,
            max_transfers,
            cancel: cancel.clone(),
        };
        async move {
	    accepter(accepter_state, signaling_router).await
	}
    });

    select! {
    	_exit = cancel.cancelled() => (),
    	done = client.sync(sync_settings) => {
	    done?;
	}
    }

    matrix_log
        .log(Some(&spinner), "Offer stopping, redacting event")
        .await?;
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
