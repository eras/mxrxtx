use serde_derive::{Deserialize, Serialize};

use matrix_sdk::ruma::events::macros::EventContent;

#[derive(Debug, Serialize, Deserialize, EventContent)]
#[ruma_event(type = "fi.variaattori.mxrxtx.webrtc", kind = ToDevice)]
pub struct ToDeviceWebRtcContent {
    // todo: include sender device id and session uuid
    pub webrtc: String,
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
