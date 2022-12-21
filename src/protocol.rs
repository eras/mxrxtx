use serde_derive::{Deserialize, Serialize};

use matrix_sdk::ruma::events::macros::EventContent;

#[derive(Debug, Serialize, Deserialize)]
pub struct WebRTCOffer {
    //    pub event_id: Box<ruma::EventId>,
    pub offer: String,
}

#[derive(Debug, Serialize, Deserialize, EventContent)]
#[ruma_event(type = "fi.variaattori.mxrxtx.request_session", kind = ToDevice)]
pub struct RequestSessionEventContent {
    pub webrtc_offer: WebRTCOffer,
}

#[derive(Debug, Serialize, Deserialize, EventContent)]
#[ruma_event(type = "fi.variaattori.mxrxtx.accept_session", kind = ToDevice)]
pub struct AcceptSessionEventContent {
    pub webrtc_offer: WebRTCOffer,
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
