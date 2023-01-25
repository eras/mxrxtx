use crate::{
    config, download,
    level_event::LevelEvent,
    matrix_common, matrix_log,
    matrix_signaling::{MatrixSignaling, SessionInfo},
    progress_common, protocol,
    transfer_session::TransferSession,
    transport,
};
use indicatif::MultiProgress;
use matrix_sdk::config::SyncSettings;
use matrix_sdk::ruma::OwnedDeviceId;
use matrix_sdk::{
    room::{Joined, Room},
    Client,
};
use std::sync::Arc;
use thiserror::Error;
use tokio::select;
use tokio::sync::mpsc;
use tokio::sync::Mutex;

#[allow(unused_imports)]
use log::{debug, error, info, warn};

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    MatrixCommonError(#[from] matrix_common::Error),

    #[error(transparent)]
    MatrixSdkError(#[from] matrix_sdk::Error),

    #[error("Error: {}", .0)]
    InternalError(String),

    #[error(transparent)]
    TransportError(#[from] transport::Error),

    #[error(transparent)]
    MatrixLogError(#[from] matrix_log::Error),
}

struct Setup {
    client: Client,
    device_id: OwnedDeviceId,
    config: config::Config,
    output_dir: String,
    rooms: Option<Vec<Joined>>,
    matrix_log: matrix_log::MatrixLog,
    multi_progress: MultiProgress,
    transfer_session: TransferSession,
    max_transfers: Option<usize>,
    exit_signal: LevelEvent,
}

struct Monitor {
    device_id: OwnedDeviceId,
    config: config::Config,
    results_send: mpsc::UnboundedSender<Result<(), Error>>,
    output_dir: String,
    rooms: Option<Vec<Joined>>,
    client: Client,
    matrix_log: Arc<Mutex<matrix_log::MatrixLog>>,
    multi_progress: MultiProgress,
    transfer_session: Arc<Mutex<TransferSession>>,
    max_transfers: Option<usize>,
    exit_signal: LevelEvent,
}

impl Monitor {
    fn new(
        setup: Setup,
    ) -> (
        Arc<Mutex<Monitor>>,
        mpsc::UnboundedReceiver<Result<(), Error>>,
    ) {
        let (results_send, results_receive) = mpsc::unbounded_channel();
        let matrix_log = Arc::new(Mutex::new(setup.matrix_log));
        let monitor = Arc::new(Mutex::new(Monitor {
            device_id: setup.device_id,
            config: setup.config,
            results_send,
            output_dir: setup.output_dir,
            rooms: setup.rooms,
            client: setup.client.clone(),
            matrix_log,
            multi_progress: setup.multi_progress,
            transfer_session: Arc::new(Mutex::new(setup.transfer_session)),
	    max_transfers: setup.max_transfers,
	    exit_signal: setup.exit_signal,
        }));
        // TODO: remove added event handlers on Drop
        setup.client.add_event_handler({
            let monitor = monitor.clone();
            move |ev: protocol::SyncOffer, room: Room| {
                let monitor = monitor.clone();
                async move {
                    let mut monitor = monitor.lock().await;
                    let result = monitor.on_offer(ev, room).await;
                    monitor.handle_error_result(result);
                }
            }
        });
        (monitor, results_receive)
    }

    fn handle_error_result(&mut self, result: Result<(), Error>) {
        match result {
            Ok(()) => (),
            result @ Err(_) => {
                // Ignore error: probably this object was collected already
                let _ = self.results_send.send(result);
            }
        }
    }

    async fn on_offer(&mut self, offer: protocol::SyncOffer, room: Room) -> Result<(), Error> {
        let client = &self.client;
        let room = match room {
            Room::Joined(joined) => joined,
            _ => return Ok(()), // ignore other rooms
        };
        let want_download = match &self.rooms {
            None => true,
            Some(rooms) => rooms
                .iter()
                .map(|x| x.room_id())
                .any(|x| x == room.room_id()),
        };
        if !want_download {
            return Ok(());
        }
        let peer_user_id = offer.sender().to_owned();
        let event_id = offer.event_id().to_owned();
        let offer_content: protocol::OfferContent = match offer {
            protocol::SyncOffer::Original(offer) => offer.content,
            protocol::SyncOffer::Redacted(_) => {
                // skip redacted offers
                return Ok(());
            }
        };
        let transfer_id = protocol::Uuid::new_v4();
        let signaling = MatrixSignaling::new(
            client.clone(),
            self.device_id.clone(),
            event_id.clone(),
            Some(SessionInfo {
                peer_user_id: peer_user_id.clone(),
                peer_device_id: None,
                id: transfer_id,
            }),
        )
        .await;
        let transport = transport::Transport::new(
            signaling,
            self.config
                .ice_servers
                .clone()
                .iter()
                .map(|x| x.as_str())
                .collect(),
        )?;
        // TODO: use locking to ensure entries to MultiProgress are made sequentially
        let progress = progress_common::make_spinner(Some(&self.multi_progress));
        // TODO: handle errors
        let _download_task = tokio::spawn({
            let matrix_log = self.matrix_log.clone();
            let output_dir = self.output_dir.clone();
            let event_id = event_id.clone();
            let multi_progress = self.multi_progress.clone();
            let peer_user_id = peer_user_id.clone();
            let transfer_session = self.transfer_session.clone();
	    let max_transfers = self.max_transfers;
	    let exit_signal = self.exit_signal.clone();
            async move {
                let matrix_log = matrix_log.clone();
                {
                    let matrix_log = matrix_log.lock().await;
                    // TODO: handle errors
                    let _ignore = matrix_log
                        .log(
                            Some(&progress),
                            &format!("Downloading event {event_id} from {peer_user_id}"),
                        )
                        .await;
                }
                // TODO: handle errors
                transfer_session.lock().await.inc_tranferring();
                let status = download::transfer(
                    output_dir,
                    transport,
                    offer_content,
                    Some(&multi_progress),
                    peer_user_id.as_ref(),
                )
                .await;
                {
                    let matrix_log = matrix_log.lock().await;
                    // TODO: handle errors
                    let _ignore = matrix_log
                        .log(
                            None,
                            &format!("Downloading of event {} finished: {:?}", event_id, status),
                        )
                        .await;
		    let num_complete = transfer_session.lock().await.inc_complete();
		    if let Some(max_transfers) = &max_transfers {
			if num_complete >= *max_transfers {
			    // TODO: handle errors
			    let _ignore = matrix_log
				.log(
				    None,
				    "Maximum number of transfers reached, exiting",
				)
				.await;
			    exit_signal.issue().await;
			}
		    }
                }
            }
        });
        Ok(())
    }
}

#[rustfmt::skip::macros(select)]
pub async fn monitor(
    config: config::Config,
    output_dir: &str,
    rooms: Option<Vec<String>>,
    max_transfers: Option<usize>,
) -> Result<(), Error> {
    let matrix_common::MatrixInit {
        client,
        device_id,
        matrix_log,
        ..
    } = matrix_common::init(&config).await?;

    let multi = MultiProgress::new();
    let spinner = progress_common::make_spinner(Some(&multi));
    matrix_log.log(Some(&spinner), "Starting monitor").await?;

    let sync_settings = SyncSettings::default();

    let rooms = match rooms {
        None => None,
        Some(rooms) => Some(
            futures::future::try_join_all(
                rooms
                    .iter()
                    .map(|room| matrix_common::get_joined_room_by_name(&client, room))
                    .collect::<Vec<_>>(),
            )
            .await?,
        ),
    };

    matrix_log.log(Some(&spinner), "Monitoring offers").await?;
    let transfer_session = TransferSession::new(&multi);

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

    let (_monitor, mut results) = Monitor::new(Setup {
        client: client.clone(),
        device_id,
        config,
        output_dir: output_dir.to_string(),
        rooms,
        matrix_log: matrix_log.clone(),
        multi_progress: multi,
        transfer_session,
	max_transfers,
	exit_signal: exit_signal.clone(),
    });
    select! {
    	_exit = exit_signal.wait() => (),
	done2 = results.recv() => {
	    done2.unwrap_or(Err(Error::InternalError(
                "Failed to read results channel".to_string(),
            )))?;
	}
	done = client.sync(sync_settings) => {
	    done?;
	}
    }
    matrix_log.log(Some(&spinner), "Monitoring stopped").await?;

    Ok(())
}
