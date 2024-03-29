use crate::{
    config, matrix_common,
    matrix_signaling::{MatrixSignaling, SessionInfo},
    progress_common, protocol, transport,
    utils::{escape, escape_paths},
    digest::file_sha512,
};
use futures::{AsyncReadExt, AsyncWriteExt};
use indicatif::MultiProgress;
use matrix_sdk::config::SyncSettings;
use matrix_sdk::ruma::{OwnedEventId, OwnedRoomId};
use sha2::{Digest, Sha512};
use std::cmp;
use std::convert::TryFrom;
use std::fs::File;
use std::io::{Write, BufWriter};
use std::path::PathBuf;
use std::str::FromStr;
use thiserror::Error;
use tokio::{self, select};

#[allow(unused_imports)]
use log::{debug, error, info, warn};

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    ConfigError(#[from] config::Error),

    #[error(transparent)]
    MatrixSdkError(#[from] matrix_sdk::Error),

    #[error(transparent)]
    MatrixUriParseError(#[from] MatrixUriParseError),

    #[error("Matrix uri does not have a room id: {}", .0)]
    MatrixUriIsNotRoomIdError(String),

    #[error("Matrix uri does not have event id: {}", .0)]
    MatrixUriMissingEventIdError(String),

    #[error("Offer was redacted")]
    OfferRedactedError,

    #[error("Matrix room not found: {}", .0)]
    NoSuchRoomError(String),

    #[error(transparent)]
    SerdeJsonError(#[from] serde_json::Error),

    #[error(transparent)]
    MatrixClientbuildError(#[from] matrix_sdk::ClientBuildError),

    #[error(transparent)]
    IdParseError(#[from] matrix_sdk::ruma::IdParseError),

    #[error(transparent)]
    OpenStoreError(#[from] matrix_sdk_sled::OpenStoreError),

    #[error(transparent)]
    TransportError(#[from] transport::Error),

    #[error(transparent)]
    IoError(#[from] std::io::Error),

    #[error(transparent)]
    MatrixCommonError(#[from] matrix_common::Error),
}

#[derive(Error, Debug)]
pub struct MatrixUriParseError(matrix_uri::MatrixUriParseError);

impl std::fmt::Display for MatrixUriParseError {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        fmt.write_fmt(format_args!("Matrix URI parse error: {:?}", self.0))
    }
}

fn mxid_from_mxid_uri(mxid: &matrix_uri::MatrixId) -> String {
    // I don't understand when the sigil is or isn't there..
    match mxid.body.chars().next() {
        Some('!' | '%' | '$' | '+' | '#' | '@') => mxid.body.clone(),
        Some(_) => match mxid.id_type {
            matrix_uri::IdType::RoomAlias
            | matrix_uri::IdType::RoomId
            | matrix_uri::IdType::EventId => {
                format!("{}{}", mxid.id_type.to_sigil(), mxid.body)
            }
            _ => mxid.body.clone(),
        },
        None => "".to_string(),
    }
}

fn get_room_id_from_uri(uri: &matrix_uri::MatrixUri) -> Result<OwnedRoomId, Error> {
    match &uri.mxid.id_type {
        matrix_uri::IdType::RoomId => {
            let mxid = mxid_from_mxid_uri(&uri.mxid);
            Ok(<&matrix_sdk::ruma::RoomId>::try_from(mxid.as_str())?.to_owned())
        }
        _ => {
            return Err(Error::MatrixUriIsNotRoomIdError(format!(
                "{:?}",
                uri.mxid.id_type
            )))
        }
    }
}

fn get_event_id_from_uri(uri: &matrix_uri::MatrixUri) -> Result<OwnedEventId, Error> {
    let event_id = match &uri.child_mxid {
        Some(child_mxid) => match child_mxid.id_type {
            matrix_uri::IdType::EventId => {
                <&matrix_sdk::ruma::EventId>::try_from(mxid_from_mxid_uri(child_mxid).as_str())?
                    .to_owned()
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
    Ok(event_id)
}

const BLOCK_SIZE: usize = 1usize << 16;

#[derive(Clone)]
pub struct Options {
    pub output_dir: String,
    pub skip_existing: bool,
}

impl Default for Options {
    fn default() -> Self {
	Options {
	    output_dir: "".to_string(),
	    skip_existing: true,
	}
    }
}

fn path_for_file(file_name: &str, options: &Options) -> Result<PathBuf, Error> {
    let mut path = PathBuf::from(&options.output_dir);
    path.push(escape_paths(file_name));
    Ok(path)
}

pub async fn check_existing_files(files: &Vec<protocol::File>,
				  multi: &MultiProgress,
				  options: &Options) -> Result<bool, Error> {
    let mut has_all_files = true;
    for offer_file in files {
	if let Some(expected) = offer_file.hashes.get("sha512") {
	    match file_sha512(&path_for_file(&offer_file.name, options)?, Some(multi)).await {
		Ok((sha512, _size)) => {
		    if sha512 != *expected {
			has_all_files = false;
		    }
		}
		Err(_) => {
		    has_all_files = false;
		}
	    }
	}
    }
    Ok(has_all_files)
}

pub async fn transfer(
    options: Options,
    mut transport: transport::Transport,
    offer_content: protocol::OfferContent,
    multi: Option<&MultiProgress>,
    prefix: &str,
) -> Result<(), Error> {
    let files = &offer_content.files;
    let multi = if let Some(multi) = multi {
        multi.clone()
    } else {
        MultiProgress::new()
    };
    if options.skip_existing {
	let has_all_files = check_existing_files(files, &multi, &options).await?;
	if has_all_files {
	    info!("File already downloaded completely, skipping");
	    return Ok(())
	}
    }
    debug!("Connecting!");
    let mut cn = transport.connect().await?;
    debug!("Connected!");
    let mut buffer: [u8; BLOCK_SIZE] = [0; BLOCK_SIZE];
    let mut eof = false;
    let mut received_bytes = 0;
    let expected_bytes = files.iter().map(|x| x.size as usize).sum();
    let mut file_idx = 0usize;
    let mut file_offset = 0usize;
    let mut cur_file_hasher: Option<(BufWriter<File>, Sha512)> = None;
    let finalize_file = |file_idx: usize, cur_file_hasher: Option<(BufWriter<File>, Sha512)>| {
        if let Some((_, hasher)) = cur_file_hasher {
            if let Some(expected) = files[file_idx].hashes.get("sha512") {
                let result = hasher.finalize();
                if result.to_vec() != expected.as_bytes() {
                    error!("Transferred file {file} had mismatching SHA512 {mismatch:x}, expected {expected}",
                           file = escape(&files[file_idx].name),
			   mismatch = &result,
			   expected = hex::encode(expected.as_bytes()),
                    );
                }
            }
        }
    };
    let overall_progress =
        progress_common::make_transfer_progress(expected_bytes as u64, Some(&multi));
    overall_progress.set_prefix(prefix.to_string());
    while !eof && file_idx < files.len() && received_bytes < expected_bytes {
        // todo: doesn't handle transferring single 0-byte file
        let mut n = match cn.read(&mut buffer).await {
            Ok(x) => x,
            Err(err) => {
                error!("Error receiving: {err}");
                // TODO: this probably happens because peer immediately closes after sending
                // everything we should acknowledge the transfer explicitly, because
                // otherwise if there is a network error, we might lose the end
                0
            }
        };
        received_bytes += n;
        overall_progress.inc(n as u64);
        eof = n == 0;
        let mut buffer_offset = 0usize;
        while n > 0 && file_idx < files.len() {
            let cur_bytes_remaining = files[file_idx].size as usize - file_offset;
            if cur_bytes_remaining == 0 {
                finalize_file(file_idx, cur_file_hasher.take());
                file_idx += 1;
                file_offset = 0usize;
            } else {
                let write_bytes = cmp::min(cur_bytes_remaining, n);
                if cur_file_hasher.is_none() {
		    let file = BufWriter::new(File::create(&path_for_file(&files[file_idx].name, &options)?)?);
                    let hasher = Sha512::new();
                    cur_file_hasher = Some((file, hasher));
                }
                match &mut cur_file_hasher {
                    Some((cur_file, hasher)) => {
                        cur_file
                            .write_all(&buffer[buffer_offset..(buffer_offset + write_bytes)])?;
                        hasher.update(&buffer[buffer_offset..(buffer_offset + write_bytes)]);
                        buffer_offset += write_bytes;
                        file_offset += write_bytes;
                        n -= write_bytes;
                    }
                    None => panic!("Impossible"), // todo: how to avoid this match?
                }
            }
        }
    }
    if file_idx < files.len() {
        finalize_file(file_idx, cur_file_hasher.take());
    }
    debug!("Exiting loop");
    cn.write_all(b"ok").await?;
    //info!("Received {received_bytes} bytes");
    transport.stop().await?;
    //info!("Transport stopped");
    Ok(())
}

#[rustfmt::skip::macros(select)]
pub async fn download(
    config: config::Config,
    urls: Vec<&str>,
    options: Options,
) -> Result<(), Error> {
    let matrix_common::MatrixInit {
        client, device_id, ..
    } = matrix_common::init(&config).await?;

    //info!("Retrieving event");
    let uri = matrix_uri::MatrixUri::from_str(urls[0]).map_err(MatrixUriParseError)?;
    let room_id = get_room_id_from_uri(&uri)?;
    let room = client
        .get_joined_room(&room_id)
        .ok_or(Error::NoSuchRoomError(String::from(room_id.as_str())))?;

    let event_id = get_event_id_from_uri(&uri)?;
    let event = room.event(event_id.as_ref()).await?;

    let offer = match serde_json::from_str::<protocol::SyncOffer>(event.event.json().get()) {
        Ok(x) => x,
        err @ Err(_) => {
            debug!("event: {event:?}");
            err?
        }
    };
    debug!("offer: {offer:?}");

    let id = protocol::Uuid::new_v4();
    let peer_user_id = offer.sender().to_owned();

    let offer_content: protocol::OfferContent = match offer {
        protocol::SyncOffer::Original(offer) => offer.content,
        protocol::SyncOffer::Redacted(_) => {
            return Err(Error::OfferRedactedError);
        }
    };

    let signaling = MatrixSignaling::new(
        client.clone(),
        device_id,
        event_id,
        Some(SessionInfo {
            peer_user_id,
            peer_device_id: None,
            id,
        }),
    )
    .await;
    let transport = transport::Transport::new(
        signaling,
        config
            .ice_servers
            .clone()
            .iter()
            .map(|x| x.as_str())
            .collect(),
    )?;

    let download_task = tokio::spawn({
        async move { transfer(options, transport, offer_content, None, "").await }
    });
    let sync_settings = SyncSettings::default().filter(matrix_common::just_joined_rooms_filter());

    select! {
    	done = client.sync(sync_settings) => {
	    done?;
	}
	_exit = download_task =>
	    (),
    }

    Ok(())
}
