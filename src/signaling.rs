use anyhow;
use async_datachannel::Message;
use async_trait::async_trait;

#[async_trait]
pub trait Signaling {
    async fn send(&mut self, message: Message) -> Result<(), anyhow::Error>;
    async fn recv(&mut self) -> Result<Option<Message>, anyhow::Error>;
    async fn close(self);
}
