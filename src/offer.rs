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
use std::io::{Read, BufReader};
use std::path::{Path, PathBuf, is_separator};
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

    #[error("Cannot convert path to string: {:?}", .0)]
    FileNameError(PathBuf),

    #[error(transparent)]
    PathStripPrefixError(#[from] std::path::StripPrefixError),
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

const BLOCK_SIZE: usize = 1usize << 16;

#[rustfmt::skip::macros(select)]
#[instrument(skip_all)]
pub async fn transfer(
    offer_files: Vec<(PathBuf, protocol::File)>,
    mut cn: transport::DataStream,
    progress: ProgressBar,
    cancel: CancellationToken,
) -> Result<(), Error> {
    let mut abort = false;
    let mut buffer: [u8; BLOCK_SIZE] = [0; BLOCK_SIZE];
    let mut total_bytes = 0;
    event!(Level::TRACE, is_cancelled=cancel.is_cancelled());
    for (offer_path, offer_file) in offer_files {
	let mut file = BufReader::new(File::open(offer_path)?);
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
    offer_files: Vec<(PathBuf, protocol::File)>,
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
            None,
            &format!("Accepted a connection, transferring file to {peer}"),
        )
        .await?;
    drop(spinner);
    let progress = {
	let files: Vec<protocol::File> =
	    offer_files.iter().map(|(_, file)| file.clone()).collect();
	make_transfer_progress(&files, Some(multi_progress))
    };
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

fn common_prefix(a: &str, b: &str) -> String {
    let mut prefix = "".to_string();
    for (a, b) in a.chars().zip(b.chars()) {
	if a == b {
	    prefix.push(a);
	} else {
	    break;
	}
    }
    prefix
}

// TODO: use std::path::Path::components
#[instrument(ret)]
fn eliminate_common_prefix_dir(offer_files: Vec<&str>) -> Result<(PathBuf, Vec<PathBuf>), Error> {
    let mut prefix =
	match offer_files.first() {
	    Some(file) => file.to_string(),
	    None => "".to_string(),
	};
    let mut result = Vec::new();
    // TODO: take case-insensitive filesystems into account? is there a thing like file identity to use?
    for file in offer_files.clone() {
	prefix = common_prefix(&prefix, file);
    }
    // prefix cut to the last directory separator
    let mut cut_prefix = String::new();
    let mut cur_chunk = String::new();
    for char in prefix.chars() {
	cur_chunk.push(char);
	if is_separator(char) {
	    cut_prefix.push_str(&cur_chunk);
	    cur_chunk.clear();
	}
    }
    let prefix = Path::new(&cut_prefix);
    event!(Level::TRACE, "prefix={:?}", prefix);
    for file in offer_files {
	event!(Level::TRACE, "file={:?}", file);
	result.push(Path::new(file).strip_prefix(prefix)?.to_path_buf());
    }
    Ok((prefix.to_path_buf(), result))
}

#[instrument]
fn remove_path_separator_prefix(name: &str) -> String {
    let mut iter = name.chars();
    let mut result = String::new();
    // first skip all path separator (and copy first non-path-separator)
    for char in iter.by_ref() {
	if !is_separator(char) {
	    result.push(char);
	    break;
	}
    }
    // then copy the rest of the chars
    for char in iter {
	result.push(char);
    }
    result.to_string()
}

#[instrument(skip(multi_progress))]
async fn make_offers_from_filenames(
    offer_files: Vec<&str>,
    multi_progress: Option<&MultiProgress>
) -> Result<Vec<(PathBuf, protocol::File)>, Error> {
    let (common_dir, offer_files) = eliminate_common_prefix_dir(offer_files)?;
    event!(Level::TRACE, "common_dir={:?}", common_dir);
    let mut result = Vec::new();
    for file in &offer_files {
	event!(Level::TRACE, "file={:?}", file);
	let file_path = {
	    let mut path = common_dir.clone();
	    path.push(file);
	    path
	};
	event!(Level::TRACE, "file_path={:?}", &file_path);
	let (sha512, size) = digest::file_sha512(&file_path, multi_progress).await?;
	let mut hashes = BTreeMap::new();
	let file_name =
	    remove_path_separator_prefix(
		&file.clone().into_os_string().into_string()
		    .map_err(|_| Error::FileNameError(file_path.to_path_buf()))?
	    );
	hashes.insert("sha512".to_string(), sha512);
	result.push(
	    (file_path.to_path_buf(),
             fs::metadata(&file_path).map(|_metadata| protocol::File {
		 // we need to get date later so let's not drop this metadata thing yet..
		 name: file_name,
		 mimetype: String::from("application/octet-stream"),
		 size, // TODO: respect this when sending file
		 thumbnail_file: None,
		 thumbnail_info: None,
		 thumbnail_url: None,
		 hashes,
             })?,
	    )
	);
    }
    Ok(result)
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

    matrix_log.log(Some(&spinner), "Calculating checksums").await?;
    let offer_files = make_offers_from_filenames(offer_files, Some(&multi_progress)).await?;

    let offer = protocol::OfferContent {
        version: get_version(),
        name: None,
        description: None,
        files: offer_files.iter().map(|(_, file)| file.clone()).collect(),
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
        let offer_session_state = Arc::new(Mutex::new(TransferSession::new_from_multiprogess(&multi_progress, "")));
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
