// Based on the emoji_verification example from the matrix-sdk

use crate::{config, matrix_common};
use std::io::Write;
use thiserror::Error;
use tokio::select;
use tokio::sync::mpsc;

use futures::stream::StreamExt;
use matrix_sdk::{
    config::SyncSettings,
    encryption::verification::{format_emojis, Emoji, SasState, SasVerification, Verification},
    ruma::{
        events::{
            key::verification::{
                request::ToDeviceKeyVerificationRequestEvent,
                start::{OriginalSyncKeyVerificationStartEvent, ToDeviceKeyVerificationStartEvent},
            },
            room::message::{MessageType, OriginalSyncRoomMessageEvent},
        },
        UserId,
    },
    Client,
};

#[allow(unused_imports)]
use log::{debug, error, info, warn};

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    RumaError(#[from] matrix_sdk::Error),

    #[error(transparent)]
    MatrixHttpError(#[from] matrix_sdk::HttpError),

    #[error(transparent)]
    MatrixCommonError(#[from] matrix_common::Error),
}

async fn wait_for_confirmation(sas: SasVerification, emoji: [Emoji; 7]) {
    if false {
        println!("\nDo the emojis match: \n{}", format_emojis(emoji));
        print!("Confirm with `yes` or cancel with `no`: ");
        std::io::stdout()
            .flush()
            .expect("We should be able to flush stdout");

        let mut input = String::new();
        std::io::stdin()
            .read_line(&mut input)
            .expect("error: unable to read user input");

        match input.trim().to_lowercase().as_ref() {
            "yes" | "true" | "ok" => sas.confirm().await.unwrap(),
            _ => sas.cancel().await.unwrap(),
        }
    } else {
        println!(
            "\nEmojis expected to be visible on the other client: \n{}",
            format_emojis(emoji)
        );
        println!("\nAutomatically accepting! If the emojis did not match, remove state directory and start over.");
        sas.confirm().await.unwrap()
    }
}

async fn print_devices(user_id: &UserId, client: &Client) {
    println!("Devices of user {user_id}");

    for device in client
        .encryption()
        .get_user_devices(user_id)
        .await
        .unwrap()
        .devices()
    {
        println!(
            "   {:<10} {:<30} {:<}",
            device.device_id(),
            device.display_name().unwrap_or("-"),
            device.is_verified()
        );
    }
}

async fn sas_verification_handler(
    client: Client,
    sas: SasVerification,
    result_send: mpsc::UnboundedSender<Result<bool, Error>>,
) {
    println!(
        "Starting verification with {} {}",
        &sas.other_device().user_id(),
        &sas.other_device().device_id()
    );
    print_devices(sas.other_device().user_id(), &client).await;
    sas.accept().await.unwrap();

    let mut stream = sas.changes();

    while let Some(state) = stream.next().await {
        match state {
            SasState::KeysExchanged {
                emojis,
                decimals: _,
            } => {
                tokio::spawn(wait_for_confirmation(
                    sas.clone(),
                    emojis
                        .expect("We only support verifications using emojis")
                        .emojis,
                ));
            }
            SasState::Done { .. } => {
                let device = sas.other_device();

                println!(
                    "Successfully verified device {} {} {:?}",
                    device.user_id(),
                    device.device_id(),
                    device.local_trust_state()
                );

                print_devices(sas.other_device().user_id(), &client).await;

                // Ignore this error: at least something was then sent or peer is gone
                let _ = result_send.send(Ok(true));

                break;
            }
            SasState::Cancelled(cancel_info) => {
                println!(
                    "The verification has been cancelled, reason: {}",
                    cancel_info.reason()
                );

                // Ignore this error: at least something was then sent or peer is gone
                let _ = result_send.send(Ok(false));

                break;
            }
            SasState::Started { .. } | SasState::Accepted { .. } | SasState::Confirmed => (),
        }
    }
}

pub async fn add_event_handlers(
    client: Client,
    result_send: mpsc::UnboundedSender<Result<bool, Error>>,
) -> matrix_sdk::Result<()> {
    client.add_event_handler(
        |ev: ToDeviceKeyVerificationRequestEvent, client: Client| async move {
            let request = client
                .encryption()
                .get_verification_request(&ev.sender, &ev.content.transaction_id)
                .await
                .expect("Request object wasn't created");

            request
                .accept()
                .await
                .expect("Can't accept verification request");
        },
    );

    client.add_event_handler({
        let result_send = result_send.clone();
        move |ev: ToDeviceKeyVerificationStartEvent, client: Client| {
            let result_send = result_send.clone();
            async move {
                if let Some(Verification::SasV1(sas)) = client
                    .encryption()
                    .get_verification(&ev.sender, ev.content.transaction_id.as_str())
                    .await
                {
                    tokio::spawn(sas_verification_handler(client, sas, result_send.clone()));
                }
            }
        }
    });

    client.add_event_handler(
        |ev: OriginalSyncRoomMessageEvent, client: Client| async move {
            if let MessageType::VerificationRequest(_) = &ev.content.msgtype {
                let request = client
                    .encryption()
                    .get_verification_request(&ev.sender, &ev.event_id)
                    .await
                    .expect("Request object wasn't created");

                request
                    .accept()
                    .await
                    .expect("Can't accept verification request");
            }
        },
    );

    client.add_event_handler({
        move |ev: OriginalSyncKeyVerificationStartEvent, client: Client| {
            let result_send = result_send.clone();
            async move {
                if let Some(Verification::SasV1(sas)) = client
                    .encryption()
                    .get_verification(&ev.sender, ev.content.relates_to.event_id.as_str())
                    .await
                {
                    tokio::spawn(sas_verification_handler(client, sas, result_send.clone()));
                }
            }
        }
    });

    Ok(())
}

#[rustfmt::skip::macros(select)]
pub async fn verify(config: config::Config) -> Result<(), Error> {
    let (client, _device_id, first_sync_response) = matrix_common::init(&config).await?;

    let (result_send, mut result_receive) = mpsc::unbounded_channel();
    add_event_handlers(client.clone(), result_send).await?;
    let sync_settings = SyncSettings::default().token(first_sync_response.next_batch);

    info!("Ready for verification");
    select! {
	result = result_receive.recv() => {
	    if let Some(result) = result {
		if result? {
		    info!("Verification completed");
		} else {
		    info!("Verification failed");
		}
	    }
	}
	done = client.sync(sync_settings) => {
	    done?;
	}
    }

    Ok(())
}
