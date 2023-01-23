use anyhow;
use async_datachannel::Message;
use async_trait::async_trait;

#[async_trait]
pub trait Signaling {
    type PeerInfo;
    async fn send(&mut self, message: Message) -> Result<(), anyhow::Error>;
    async fn recv(&mut self) -> Result<Option<Message>, anyhow::Error>;
    async fn close(self);
    async fn get_peer_info(&self) -> Self::PeerInfo;
}

#[async_trait]
pub trait SignalingRouter {
    type Signaling: Signaling;
    async fn accept(&mut self) -> Result<Self::Signaling, anyhow::Error>;
}
