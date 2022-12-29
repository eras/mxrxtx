use serde_derive::{Deserialize, Serialize};

use matrix_sdk::ruma::events::macros::EventContent;

#[derive(Debug, Serialize, Deserialize, EventContent)]
#[ruma_event(type = "fi.variaattori.mxrxtx.webrtc_offer", kind = ToDevice)]
pub struct WebRTCOfferContent {
    pub webrtc_offer: String,
}

#[derive(Debug, Serialize, Deserialize, EventContent)]
#[ruma_event(type = "fi.variaattori.mxrxtx.webrtc_answer", kind = ToDevice)]
pub struct WebRTCAnswerContent {
    pub webrtc_answer: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct File {
    pub name: String,
    pub content_type: String,
    pub size: u64,
}

#[derive(Debug, Serialize, Deserialize, EventContent)]
#[ruma_event(type = "fi.variaattori.mxrxtx.offer", kind = MessageLike)]
pub struct OfferContent {
    pub files: Vec<File>,
}
