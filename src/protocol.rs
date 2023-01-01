use matrix_sdk::ruma::events::macros::EventContent;
use matrix_sdk::ruma::{OwnedDeviceId, OwnedEventId};
use serde_derive::{Deserialize, Serialize};

pub type Uuid = uuid::Uuid;

#[derive(Debug, Serialize, Deserialize, EventContent, Clone)]
#[ruma_event(type = "fi.variaattori.mxrxtx.webrtc", kind = ToDevice)]
pub struct ToDeviceWebRtcContent {
    // unique id identifying this webrtc handshake
    pub id: Uuid,

    #[serde(skip_serializing_if = "Option::is_none")]
    // device id of the client sending this event; needed only on first contact
    pub device_id: Option<OwnedDeviceId>,

    #[serde(skip_serializing_if = "Option::is_none")]
    // the event holding the OfferContent relevant to this session; needed only on first contact
    pub event_id: Option<OwnedEventId>,

    pub webrtc: String, // webrtc handshake data
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct File {
    pub name: String,
    pub content_type: String,
    pub size: u64,
}

#[derive(Debug, Serialize, Deserialize, EventContent, Default, Clone)]
#[ruma_event(type = "fi.variaattori.mxrxtx.offer", kind = MessageLike)]
pub struct OfferContent {
    pub files: Vec<File>,
}
