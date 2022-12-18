use serde_derive::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct SessionInfo {
    pub event_id: ruma::EventId,
    pub webrtc_ice: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub enum MxrxtxEvent {
    RequestSession(SessionInfo),
    AcceptSession(SessionInfo),
}
