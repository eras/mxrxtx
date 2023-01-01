use crate::signaling::Signaling;
use async_datachannel::Message;
use async_trait::async_trait;
use futures::channel::mpsc;
use futures::stream::StreamExt;
use futures::SinkExt;

pub struct TestSignaling {
    label: &'static str,
    rx: mpsc::Receiver<String>,
    tx: mpsc::Sender<String>,
}

impl TestSignaling {
    pub fn new(label: &'static str, rx: mpsc::Receiver<String>, tx: mpsc::Sender<String>) -> Self {
        TestSignaling { label, rx, tx }
    }
}

#[async_trait]
impl Signaling for TestSignaling {
    async fn send(&mut self, message: Message) -> Result<(), anyhow::Error> {
        println!("{} sends a message {:?}", self.label, &message);
        self.tx
            .send(serde_json::to_string(&message).unwrap())
            .await
            .unwrap();
        Ok(())
    }

    async fn recv(&mut self) -> Result<Option<Message>, anyhow::Error> {
        let msg = self
            .rx
            .next()
            .await
            .map(|msg| serde_json::from_str::<Message>(&msg).unwrap());
        println!("{} received a message {:?}", self.label, &msg);
        Ok(msg)
    }

    async fn close(self) {}
}
