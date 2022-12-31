use crate::{protocol, signaling::Signaling};
use async_datachannel::Message;
use async_trait::async_trait;
use core::fmt;
use futures::{
    channel::{mpsc, oneshot},
    stream::StreamExt,
    SinkExt,
};
//use matrix_sdk::ruma::events::AnyToDeviceEvent;
use anyhow;
use matrix_sdk::{event_handler::EventHandlerHandle, Client};
use ruma::OwnedUserId;
use ruma_client_api;
use serde::{de::DeserializeOwned, Serialize};
use std::sync::Arc;
use tokio::{self, sync::Mutex};

type Events = ruma_client_api::sync::sync_events::v3::ToDevice;

pub struct MatrixSignaling {
    client: Client,
    events_rx: mpsc::Receiver<Message>,
    peer_user_id: Arc<Mutex<Option<OwnedUserId>>>,
    handler_handle: Arc<Mutex<Option<EventHandlerHandle>>>,
}

impl MatrixSignaling {
    pub async fn new(client: Client, peer_user_id: Option<OwnedUserId>) -> Self {
        let peer_user_id = Arc::new(Mutex::new(peer_user_id));
        let (events_tx, events_rx) = mpsc::channel(32);
        let events_tx = Arc::new(Mutex::new(events_tx));
        let handler_handle = Arc::new(Mutex::new(None));
        {
            let peer_user_id = peer_user_id.clone();
            *handler_handle.lock().await = Some(client.add_event_handler({
                let events_tx = events_tx.clone();
                let peer_user_id = peer_user_id.clone();
                move |event: protocol::ToDeviceWebRtc| {
                    println!("MatrixSignaling: Cool: {event:?}");
                    let message = serde_json::from_str(&event.content.webrtc).unwrap();
                    let events_tx = events_tx.clone();
                    let peer_user_id = peer_user_id.clone();
                    async move {
                        let mut peer_user_id = peer_user_id.lock().await;
                        if peer_user_id.is_none() {
                            *peer_user_id = Some(event.sender.to_owned());
                        }
                        if let Err(err) = events_tx.lock().await.send(message).await {
                            println!("Failed to send message: {err}");
                        }
                    }
                }
            }));
        }
        MatrixSignaling {
            client,
            events_rx,
            peer_user_id,
            handler_handle,
        }
    }
}

#[async_trait]
impl Signaling for MatrixSignaling {
    async fn send(&mut self, message: Message) -> Result<(), anyhow::Error> {
        println!("MatrixSignaling: send: {message:?}");
        if let Some(peer_user_id) = self.peer_user_id.lock().await.clone() {
            let txn_id = ruma::TransactionId::new();
            use ruma::events::AnyToDeviceEventContent;
            use ruma::serde::Raw;
            use ruma_client_api::to_device::send_event_to_device;
            use ruma_common::to_device::DeviceIdOrAllDevices;
            use std::collections::BTreeMap;
            type Foo = BTreeMap<DeviceIdOrAllDevices, Raw<AnyToDeviceEventContent>>;
            let all = DeviceIdOrAllDevices::AllDevices;

            let webrtc = protocol::ToDeviceWebRtcContent {
                webrtc: serde_json::to_string(&message).unwrap(),
            };

            let webrtc_event: Raw<AnyToDeviceEventContent> =
                Raw::from_json(serde_json::value::to_raw_value(&webrtc)?);

            let values: Foo = vec![(all, webrtc_event)].into_iter().collect();

            let mut messages = send_event_to_device::v3::Messages::new();
            messages.insert(peer_user_id, values);
            let request = send_event_to_device::v3::Request::new_raw(
                "fi.variaattori.mxrxtx.webrtc",
                &txn_id,
                messages,
            );

            println!("MatrixSignaling: send locking");
            self.client.send(request, None).await?;
            println!("MatrixSignaling: done sending");
        } else {
            println!("MatrixSignaling: no peer user id, cannot send");
        }
        Ok(())
    }

    // vai sittenkin callback?
    async fn recv(&mut self) -> Result<Option<Message>, anyhow::Error> {
        let x = self.events_rx.next().await;
        println!("MatrixSignaling: recv: {x:?}");
        Ok(x)
    }

    async fn close(mut self) {
        println!("MatrixSignaling: closing");
        (self.handler_handle.lock().await.take()).map(|x| self.client.remove_event_handler(x));
        println!("MatrixSignaling: closed");
    }
}
