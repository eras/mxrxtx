use crate::{protocol, signaling::Signaling};
use async_datachannel::Message;
use async_trait::async_trait;
use futures::{channel::mpsc, stream::StreamExt, SinkExt};
//use matrix_sdk::ruma::events::AnyToDeviceEvent;
use anyhow;
use matrix_sdk::{event_handler::EventHandlerHandle, Client};
use ruma::{OwnedDeviceId, OwnedEventId, OwnedUserId};
use ruma_client_api;
use std::sync::Arc;
use tokio::{self, sync::Mutex};

#[derive(Clone, Debug)]
pub struct SessionInfo {
    pub peer_user_id: OwnedUserId,
    pub id: protocol::Uuid,
    pub peer_device_id: Option<OwnedDeviceId>,
}

pub struct MatrixSignaling {
    device_id: OwnedDeviceId,
    event_id: OwnedEventId,
    client: Client,
    session_info: Arc<Mutex<Option<SessionInfo>>>,
    events_rx: mpsc::Receiver<Message>,
    handler_handle: Arc<Mutex<Option<EventHandlerHandle>>>,
    first_send: bool, // used to avoid sending same fields in many messages
}

impl MatrixSignaling {
    pub async fn new(
        client: Client,
        device_id: OwnedDeviceId,
        event_id: OwnedEventId,
        session_info: Option<SessionInfo>,
    ) -> Self {
        let session_info = Arc::new(Mutex::new(session_info));
        let (events_tx, events_rx) = mpsc::channel(32);
        let events_tx = Arc::new(Mutex::new(events_tx));
        let handler_handle = Arc::new(Mutex::new(None));
        {
            let session_info = session_info.clone();
            *handler_handle.lock().await = Some(client.add_event_handler({
                let events_tx = events_tx.clone();
                let event_id = event_id.clone();
                let session_info = session_info.clone();
                move |event: protocol::ToDeviceWebRtc| {
                    println!("MatrixSignaling: Cool: {event:?}");
                    let events_tx = events_tx.clone();
                    let event_id = event_id.clone();
                    let session_info = session_info.clone();
                    async move {
                        match serde_json::from_str(&event.content.webrtc) {
                            Err(err) => {
                                println!(
                                    "MatrixSignaling: failed to deserialize message ({:?}), skipping",
				    err
                                );
                            }
                            Ok(message) => {
                                let mut session_info = session_info.lock().await;
                                let id = event.content.id;
                                let send;
                                if event
                                    .content
                                    .event_id
                                    .clone()
                                    .map(|event_event_id| event_event_id == event_id)
                                    .unwrap_or(true)
                                {
                                    match &*session_info {
                                        None => {
                                            let peer_user_id = event.sender.to_owned();
                                            let peer_device_id = event.content.device_id.clone();
                                            *session_info = Some(SessionInfo {
                                                peer_user_id,
                                                peer_device_id,
                                                id,
                                            });
                                            send = true;
                                        }
                                        Some(session_info) => {
                                            if session_info.id != id {
                                                println!(
						    "Ignoring event with unknown id {} vs current {}",
						    id, session_info.id
						);
                                                send = false;
                                            } else {
                                                send = true;
                                            }
                                        }
                                    }
                                } else {
                                    println!(
                                        "Ignoring event with unknown event id {} vs current {}",
                                        &event.content.event_id.expect(
                                            "Previous condition should have made this impossible"
                                        ),
                                        event_id
                                    );
                                    send = false;
                                }
                                if send {
                                    if let Err(err) = events_tx.lock().await.send(message).await {
                                        println!("Failed to send message: {err}");
                                    }
                                }
                            }
                        }
                    }
                }
            }));
        }
        MatrixSignaling {
            client,
            events_rx,
            session_info,
            handler_handle,
            device_id,
            event_id,
            first_send: true,
        }
    }
}

#[async_trait]
impl Signaling for MatrixSignaling {
    async fn send(&mut self, message: Message) -> Result<(), anyhow::Error> {
        println!("MatrixSignaling: send: {message:?}");
        if let Some(session_info) = self.session_info.lock().await.clone() {
            let txn_id = ruma::TransactionId::new();
            use ruma::events::AnyToDeviceEventContent;
            use ruma::serde::Raw;
            use ruma_client_api::to_device::send_event_to_device;
            use ruma_common::to_device::DeviceIdOrAllDevices;
            use std::collections::BTreeMap;
            type Foo = BTreeMap<DeviceIdOrAllDevices, Raw<AnyToDeviceEventContent>>;

            let webrtc = protocol::ToDeviceWebRtcContent {
                webrtc: serde_json::to_string(&message)?,
                id: session_info.id,
                device_id: if self.first_send {
                    Some(self.device_id.clone())
                } else {
                    None
                },
                event_id: if self.first_send {
                    Some(self.event_id.clone())
                } else {
                    None
                },
            };
            self.first_send = false;

            let webrtc_event: Raw<AnyToDeviceEventContent> =
                Raw::from_json(serde_json::value::to_raw_value(&webrtc)?);

            let values: Foo = vec![(
                session_info
                    .peer_device_id
                    .map(DeviceIdOrAllDevices::DeviceId)
                    .unwrap_or(DeviceIdOrAllDevices::AllDevices),
                webrtc_event,
            )]
            .into_iter()
            .collect();

            let mut messages = send_event_to_device::v3::Messages::new();
            messages.insert(session_info.peer_user_id.clone(), values);
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
        if let Some(x) = self.handler_handle.lock().await.take() {
            self.client.remove_event_handler(x);
        }
        println!("MatrixSignaling: closed");
    }
}
