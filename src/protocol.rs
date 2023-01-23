use matrix_sdk::ruma::events::macros::EventContent;
use matrix_sdk::ruma::events::room::{EncryptedFile, ThumbnailInfo};
use matrix_sdk::ruma::serde::Base64;
use matrix_sdk::ruma::{OwnedDeviceId, OwnedEventId};
use serde_derive::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub type Uuid = uuid::Uuid;

#[derive(Debug, Serialize, Deserialize, EventContent, Clone)]
#[ruma_event(type = "fi.variaattori.mxrxtx.webrtc", kind = ToDevice)]
pub struct ToDeviceWebRtcContent {
    // unique id identifying this webrtc handshake
    pub id: Uuid,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    // device id of the client sending this event; needed only on first contact
    pub device_id: Option<OwnedDeviceId>,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    // the event holding the OfferContent relevant to this session; needed only on first contact
    pub event_id: Option<OwnedEventId>,

    pub webrtc: String, // webrtc handshake data
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct File {
    pub name: String,

    pub mimetype: String,

    pub size: u64,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thumbnail_file: Option<EncryptedFile>,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thumbnail_info: Option<ThumbnailInfo>,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thumbnail_url: Option<String>,

    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub hashes: BTreeMap<String, Base64>,
}

#[derive(Debug, Serialize, Deserialize, EventContent, Default, Clone)]
#[ruma_event(type = "fi.variaattori.mxrxtx.offer", kind = MessageLike)]
pub struct OfferContent {
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub version: String,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,

    pub files: Vec<File>,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thumbnail_info: Option<ThumbnailInfo>,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thumbnail_url: Option<String>,
}
