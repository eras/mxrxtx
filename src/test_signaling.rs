use crate::signaling::{Signaling, SignalingRouter};
use async_datachannel::Message;
use async_trait::async_trait;
use futures::channel::mpsc;
use futures::stream::StreamExt;
use futures::SinkExt;
use std::sync::Arc;
use tokio::sync::Mutex;

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

#[derive(Clone)]
pub struct TestSignalingRouter {
    tx: Arc<Mutex<mpsc::Sender<TestSignaling>>>,
    rx: Arc<Mutex<mpsc::Receiver<TestSignaling>>>,
}

impl TestSignalingRouter {
    pub fn new() -> Self {
        let (tx, rx) = mpsc::channel(32);
        let tx = Arc::new(Mutex::new(tx));
        let rx = Arc::new(Mutex::new(rx));
        Self { tx, rx }
    }

    pub async fn connect(&mut self) -> TestSignaling {
        let (here_tx, here_rx) = mpsc::channel::<String>(32);
        let (there_tx, there_rx) = mpsc::channel::<String>(32);
        let here = TestSignaling::new("download", here_rx, there_tx);
        let there = TestSignaling::new("offer", there_rx, here_tx);
        self.tx.lock().await.send(there).await.unwrap();
        here
    }
}

impl Default for TestSignalingRouter {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl SignalingRouter for TestSignalingRouter {
    type Signaling = TestSignaling;

    async fn accept(&mut self) -> Result<Self::Signaling, anyhow::Error> {
        Ok(self.rx.lock().await.next().await.unwrap())
    }
}
