use crate::{
    protocol,
    signaling::{Signaling, SignalingRouter},
};
use async_datachannel::Message;
use async_trait::async_trait;
use futures::{channel::mpsc, stream::StreamExt, SinkExt};
use matrix_sdk::ruma::{OwnedDeviceId, OwnedEventId, OwnedUserId};
use matrix_sdk::{event_handler::EventHandlerHandle, Client};
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;
use tokio::{self, sync::Mutex};

#[allow(unused_imports)]
use log::{debug, error, info, warn};

#[derive(Clone, Debug)]
pub struct SessionInfo {
    pub peer_user_id: OwnedUserId,
    pub id: protocol::Uuid,
    pub peer_device_id: Option<OwnedDeviceId>,
}

pub struct MatrixSignalingSingle {
    device_id: OwnedDeviceId,
    event_id: OwnedEventId,
    client: Client,
    session_info: Arc<Mutex<Option<SessionInfo>>>,
    events_rx: mpsc::Receiver<Message>,
    events_tx: mpsc::Sender<Message>,
    first_send: bool, // used to avoid sending same fields in many messages
}

pub struct MatrixSignaling {
    signaling: MatrixSignalingSingle,
    handler_handle: Arc<Mutex<Option<EventHandlerHandle>>>,
}

fn update_session_info(
    session_info: &mut Option<SessionInfo>,
    event: &protocol::ToDeviceWebRtc,
    id: protocol::Uuid,
) -> bool {
    let forward;
    match &mut *session_info {
        None => {
            let peer_user_id = event.sender.to_owned();
            let peer_device_id = event.content.device_id.clone();
            *session_info = Some(SessionInfo {
                peer_user_id,
                peer_device_id,
                id,
            });
            forward = true;
        }
        Some(session_info) => {
            forward = session_info.id == id;
            if forward {
                if let (Some(_), None) = (&event.content.device_id, &session_info.peer_device_id) {
                    session_info.peer_device_id = event.content.device_id.clone();
                }
            } else {
                debug!(
                    "Ignoring event with unknown id {} vs current {}",
                    id, session_info.id
                );
            }
        }
    }
    forward
}

async fn matrix_signaling_event_handler(
    local_device_id: OwnedDeviceId,
    event: protocol::ToDeviceWebRtc,
    events_tx: mpsc::Sender<Message>,
    event_id: OwnedEventId,
    session_info: Arc<Mutex<Option<SessionInfo>>>,
) {
    let mut events_tx = events_tx.clone();
    let event_id = event_id.clone();
    let session_info = session_info.clone();
    debug!("matrix_signaling_event_handler: Handling event {event:?}");
    if event.content.device_id == Some(local_device_id) {
        debug!("matrix_signaling_event_handler: ignoring message from self");
    } else {
        match serde_json::from_str::<Message>(&event.content.webrtc) {
            Err(err) => {
                error!(
                    "matrix_signaling_event_handler: failed to deserialize message ({:?}), skipping",
                    err
                );
            }
            Ok(message) => {
                let mut session_info = session_info.lock().await;
                let id = event.content.id;
                if event
                    .content
                    .event_id
                    .clone()
                    .map(|event_event_id| event_event_id == event_id)
                    .unwrap_or(true)
                {
                    if update_session_info(&mut session_info, &event, id) {
                        if let Err(err) = events_tx.send(message).await {
                            error!("Failed to send message: {err}");
                        }
                    }
                } else {
                    debug!(
                        "Ignoring event with unknown event id {} vs current {}",
                        &event
                            .content
                            .event_id
                            .expect("Previous condition should have made this impossible"),
                        event_id
                    );
                }
            }
        }
    }
}

impl MatrixSignalingSingle {
    pub async fn new(
        client: Client,
        device_id: OwnedDeviceId,
        event_id: OwnedEventId,
        session_info: Arc<Mutex<Option<SessionInfo>>>,
    ) -> Self {
        let (events_tx, events_rx) = mpsc::channel(32);
        MatrixSignalingSingle {
            client,
            events_rx,
            events_tx,
            session_info,
            device_id,
            event_id,
            first_send: true,
        }
    }
}

#[async_trait]
impl Signaling for MatrixSignalingSingle {
    async fn send(&mut self, message: Message) -> Result<(), anyhow::Error> {
        debug!("MatrixSignalingSingle::send({message:?})");
        if let Some(session_info) = self.session_info.lock().await.clone() {
            let txn_id = matrix_sdk::ruma::TransactionId::new();
            use matrix_sdk::ruma::api::client::to_device::send_event_to_device;
            use matrix_sdk::ruma::events::AnyToDeviceEventContent;
            use matrix_sdk::ruma::serde::Raw;
            use matrix_sdk::ruma::to_device::DeviceIdOrAllDevices;
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
                "fi.variaattori.mxrxtx.webrtc".into(),
                txn_id,
                messages,
            );

            debug!("MatrixSignalingSingle::send: client.send({:?})", request);
            self.client.send(request, None).await?;
        } else {
            error!("MatrixSignalingSingle::send: no peer user id, cannot send");
        }
        Ok(())
    }

    async fn recv(&mut self) -> Result<Option<Message>, anyhow::Error> {
        let x = self.events_rx.next().await;
        debug!("MatrixSignalingSingle::recv: {x:?}");
        Ok(x)
    }

    async fn close(mut self) {}
}

impl MatrixSignaling {
    pub async fn new(
        client: Client,
        device_id: OwnedDeviceId,
        event_id: OwnedEventId,
        session_info: Option<SessionInfo>,
    ) -> Self {
        let session_info = Arc::new(Mutex::new(session_info));
        let signaling = MatrixSignalingSingle::new(
            client.clone(),
            device_id.clone(),
            event_id.clone(),
            session_info.clone(),
        )
        .await;

        let events_tx = signaling.events_tx.clone();
        let handler_handle = Arc::new(Mutex::new(None));
        {
            let events_tx = events_tx.clone();
            let device_id = device_id.clone();
            *handler_handle.lock().await = Some(client.add_event_handler({
                let event_id = event_id.clone();
                let device_id = device_id.clone();
                move |event: protocol::ToDeviceWebRtc| {
                    let events_tx = events_tx.clone();
                    let device_id = device_id.clone();
                    let event_id = event_id.clone();
                    let session_info = session_info.clone();
                    matrix_signaling_event_handler(
                        device_id,
                        event,
                        events_tx,
                        event_id,
                        session_info,
                    )
                }
            }));
        }

        Self {
            signaling,
            handler_handle,
        }
    }
}

#[async_trait]
impl Signaling for MatrixSignaling {
    async fn send(&mut self, message: Message) -> Result<(), anyhow::Error> {
        self.signaling.send(message).await
    }

    async fn recv(&mut self) -> Result<Option<Message>, anyhow::Error> {
        self.signaling.recv().await
    }

    async fn close(mut self) {
        debug!("MatrixSignaling: closing");
        // remove handler first so no callbacks arrive after this
        if let Some(x) = self.handler_handle.lock().await.take() {
            self.signaling.client.remove_event_handler(x);
        }
        self.signaling.close().await;
        debug!("MatrixSignaling: closed");
    }
}

type PeerMap = Arc<Mutex<HashMap<protocol::Uuid, mpsc::Sender<Message>>>>;

pub struct MatrixSignalingRouter {
    new_peers_rx: mpsc::Receiver<MatrixSignalingSingle>, // new detected peers
}

async fn matrix_signaling_router_event_handler(
    event: protocol::ToDeviceWebRtc,
    peer_map: PeerMap,
    client: Client,
    local_device_id: OwnedDeviceId, // local device id
    event_id: OwnedEventId,         // event id holding the offer
    new_peers_tx: mpsc::Sender<MatrixSignalingSingle>, // new detected peers
) {
    let mut new_peers_tx = new_peers_tx.clone();
    let event_id = event_id.clone();
    let peer_map = peer_map.clone();
    let client = client.clone();
    let device_id = local_device_id.clone();
    debug!(
        "matrix_signaling_router_event_handler: handling event {:?}",
        &event
    );
    if event.content.device_id == Some(local_device_id) {
        debug!("MatrixSignalingSingle: ignoring message from self");
    } else {
        match serde_json::from_str::<Message>(&event.content.webrtc) {
            Err(err) => {
                error!(
                    "matrix_signaling_router_event_handler: failed to deserialize message ({:?}), skipping",
                    err
		);
            }
            Ok(message) => {
                let peer_user_id = event.sender.to_owned();
                let peer_device_id = event.content.device_id.clone();
                let id = event.content.id;
                let mut peer_map = peer_map.lock().await;
                if let Some(message_sink) = peer_map.get_mut(&id) {
                    let mut message_sink = message_sink.clone();
                    match message_sink.send(message).await {
                        Ok(()) => (),
                        Err(_err) => {
                            error!("Signaling peer {} disconnected", &id);
                            drop(message_sink);
                            peer_map.remove(&id);
                        }
                    }
                } else {
                    info!(
                        "New handshake {} from {:?} device {:?}",
                        id, &peer_user_id, &peer_device_id
                    );
                    let session_info = SessionInfo {
                        peer_user_id,
                        peer_device_id,
                        id,
                    };
                    let mut signaling = MatrixSignalingSingle::new(
                        client.clone(),
                        device_id.clone(),
                        event_id.clone(),
                        Arc::new(Mutex::new(Some(session_info))),
                    )
                    .await;
                    signaling.events_tx.send(message).await.unwrap();
                    peer_map.insert(id, signaling.events_tx.clone());
                    new_peers_tx.send(signaling).await.unwrap();
                }
            }
        }
    }
}

impl MatrixSignalingRouter {
    pub async fn new(client: Client, device_id: OwnedDeviceId, event_id: OwnedEventId) -> Self {
        let (new_peers_tx, new_peers_rx) = mpsc::channel(32);
        let handler_handle = Arc::new(Mutex::new(None));
        let peer_map: PeerMap = Arc::new(Mutex::new(HashMap::new()));
        {
            *handler_handle.lock().await = Some(client.add_event_handler({
                let peer_map = peer_map.clone();
                let client = client.clone();
                let device_id = device_id.clone();
                let event_id = event_id.clone();
                move |event: protocol::ToDeviceWebRtc| {
                    let peer_map = peer_map.clone();
                    let client = client.clone();
                    let device_id = device_id.clone();
                    let event_id = event_id.clone();
                    let new_peers_tx = new_peers_tx.clone();
                    matrix_signaling_router_event_handler(
                        event,
                        peer_map,
                        client,
                        device_id,
                        event_id,
                        new_peers_tx,
                    )
                }
            }));
        }
        MatrixSignalingRouter { new_peers_rx }
    }
}

#[async_trait]
impl SignalingRouter for MatrixSignalingRouter {
    type Signaling = MatrixSignalingSingle;

    async fn accept(&mut self) -> Result<Self::Signaling, anyhow::Error> {
        Ok(self.new_peers_rx.next().await.unwrap()) // TODO: handle unwrap
    }
}
