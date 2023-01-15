use crate::{
    config, download, matrix_common,
    matrix_signaling::{MatrixSignaling, SessionInfo},
    protocol, transport,
};
use matrix_sdk::config::SyncSettings;
use matrix_sdk::ruma::OwnedDeviceId;
use matrix_sdk::Client;
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
    RumaError(#[from] matrix_sdk::Error),

    #[error("Error: {}", .0)]
    InternalError(String),

    #[error(transparent)]
    TransportError(#[from] transport::Error),
}

struct Monitor {
    device_id: OwnedDeviceId,
    config: config::Config,
    results_send: mpsc::UnboundedSender<Result<(), Error>>,
    output_dir: String,
}

impl Monitor {
    fn new(
        client: &Client,
        device_id: OwnedDeviceId,
        config: config::Config,
        output_dir: String,
    ) -> (
        Arc<Mutex<Monitor>>,
        mpsc::UnboundedReceiver<Result<(), Error>>,
    ) {
        let (results_send, results_receive) = mpsc::unbounded_channel();
        let monitor = Arc::new(Mutex::new(Monitor {
            device_id,
            config,
            results_send,
            output_dir,
        }));
        // TODO: remove added event handlers on Drop
        client.add_event_handler({
            let monitor = monitor.clone();
            move |ev: protocol::SyncOffer, client: Client| {
                let monitor = monitor.clone();
                async move {
                    let mut monitor = monitor.lock().await;
                    let result = monitor.on_offer(ev, client).await;
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

    async fn on_offer(&mut self, offer: protocol::SyncOffer, client: Client) -> Result<(), Error> {
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
            event_id,
            Some(SessionInfo {
                peer_user_id,
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
        let _download_task = tokio::spawn({
            let output_dir = self.output_dir.clone();
            async move { download::transfer(output_dir, transport, offer_content).await }
        });
        Ok(())
    }
}

#[rustfmt::skip::macros(select)]
pub async fn monitor(config: config::Config, output_dir: &str) -> Result<(), Error> {
    let (client, device_id, first_sync_response) = matrix_common::init(&config).await?;

    let sync_settings = SyncSettings::default().token(first_sync_response.next_batch);

    info!("Finished initial sync, waiting for offers");
    let (_monitor, mut results) = Monitor::new(&client, device_id, config, output_dir.to_string());
    select! {
	done2 = results.recv() => {
	    done2.unwrap_or(Err(Error::InternalError(
                "Failed to read results channel".to_string(),
            )))?;
	}
	done = client.sync(sync_settings) => {
	    done?;
	}
    }

    Ok(())
}
