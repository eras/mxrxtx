use crate::signaling::Signaling;
use anyhow;
use thiserror::Error;

use serde::{Deserialize, Serialize};
use uuid::Uuid;

use async_datachannel::{DataStream, Message, PeerConnection, RtcConfig};
use futures::channel::{mpsc, oneshot};
use futures::stream::StreamExt;
use futures::SinkExt;

use tokio::{self, select};

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    AnyhowError(#[from] anyhow::Error),
}

#[derive(Debug, Serialize, Deserialize)]
struct ConnectionMsg {
    dest_id: Uuid,
    // kind: MsgKind,
}

enum State {
    PeerConnection(PeerConnection),
}

pub struct Transport {
    state: Option<State>,
    worker: Option<tokio::task::JoinHandle<()>>,
    stop_tx: Option<oneshot::Sender<()>>,
}

#[rustfmt::skip::macros(select)]
async fn handle_signaling(
    mut rx_sig_outbound: mpsc::Receiver<Message>,
    mut tx_sig_inbound: mpsc::Sender<Message>,
    mut signaling: impl Signaling,
    mut rx_stop: oneshot::Receiver<()>,
) {
    let mut closed = false;
    while !closed {
        select! {
            sig = rx_sig_outbound.next() => {
            	println!("handle_signaling: Wants to send something out: {sig:?}");
		match sig {
		    Some(msg) =>
             		signaling.send(msg).await.unwrap(),
		    None => {
			println!("handle_signaling: Signaling channel is closed (rx_sig_outbound)");
			closed = true;
		    }
		}
            }
            sig = signaling.recv() => {
		match sig {
		    Ok(Some(msg)) => {
			println!("handle_signaling: Received something in: {msg:?}");
			tx_sig_inbound.send(msg).await.unwrap();
		    },
		    Ok(None) => {
			println!("handle_signaling: Signaling channel is closed (tx_sig_inbound)");
			closed = true;
		    }
		    Err(err) => {
			println!("handle_signaling: Signaling channel is closed due to error: {err:?}");
			closed = true;
		    }
		}
            }
	    sig = &mut rx_stop => {
		println!("handle_signaling: Received stop_tx signal {sig:?}, exiting");
		closed = true;
	    }
        }
    }
    signaling.close().await;
}

impl Transport {
    pub fn new(signaling: impl Signaling + Send + Sync + Sync + 'static) -> Result<Self, Error> {
        let ice_servers = vec!["stun:stun.l.google.com:19302"];
        let rtc_config = RtcConfig::new(&ice_servers);
        let (tx_sig_outbound, rx_sig_outbound) = mpsc::channel(32);
        let (tx_sig_inbound, rx_sig_inbound) = mpsc::channel(32);
        let listener = PeerConnection::new(&rtc_config, (tx_sig_outbound, rx_sig_inbound))?;
        let (stop_tx, stop_rx) = oneshot::channel();
        let worker = tokio::spawn(async move {
            handle_signaling(rx_sig_outbound, tx_sig_inbound, signaling, stop_rx).await
        });
        Ok(Transport {
            state: Some(State::PeerConnection(listener)),
            worker: Some(worker),
            stop_tx: Some(stop_tx),
        })
    }

    //async fn start(&mut self) {}

    pub async fn stop(&mut self) -> Result<(), Error> {
        println!("Disconnecting");
        println!("Sending to stop_tx");
        if let Err(()) = self.stop_tx.take().unwrap().send(()) {
            println!("Stop_tx peer already dropped");
        }
        println!("Done sending to stop_tx");
        self.state = None;
        if let Some(worker) = self.worker.take() {
            worker.await.unwrap();
        }
        println!("Done disconnecting");
        Ok(())
    }

    pub async fn connect(&mut self) -> Result<DataStream, Error> {
        println!("Dialing connection");
        match &self.state {
            Some(State::PeerConnection(peer_connection)) => {
                let stream = (*peer_connection).dial("hello").await?;
                println!("Pretty cool, dialed a connection");
                Ok(stream)
            }
            _ => {
                panic!("Nope");
            }
        }
    }

    pub async fn accept(&mut self) -> Result<DataStream, Error> {
        println!("Accepting connection");
        match &mut self.state {
            Some(State::PeerConnection(peer_connection)) => {
                let stream = (*peer_connection).accept().await?;
                println!("Pretty cool, accepted a connection");
                Ok(stream)
            }
            _ => {
                panic!("Nope");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use async_trait::async_trait;
    use futures::{AsyncReadExt, AsyncWriteExt};

    struct TestSignaling {
        label: &'static str,
        rx: mpsc::Receiver<String>,
        tx: mpsc::Sender<String>,
    }

    impl TestSignaling {
        fn new(label: &'static str, rx: mpsc::Receiver<String>, tx: mpsc::Sender<String>) -> Self {
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

    #[tokio::test]
    async fn test_signaling() {
        println!("start");
        let (here_tx, here_rx) = mpsc::channel::<String>(32);
        let (there_tx, there_rx) = mpsc::channel::<String>(32);
        let mut here =
            Transport::new(TestSignaling::new("here", here_rx, there_tx)).expect("weird");
        let mut there =
            Transport::new(TestSignaling::new("there", there_rx, here_tx)).expect("weird");
        let there_task = tokio::spawn({
            async move {
                println!("there accepting connection");
                let mut conn = there.accept().await.unwrap();
                let mut buf = vec![0; 32];
                let n = conn.read(&mut buf).await.unwrap();
                drop(conn);
                let buf = &buf[0..n];
                println!("moi {buf:?}");
                there.stop().await.unwrap();
            }
        });
        let mut conn = here.connect().await.unwrap();
        conn.write(b"Hello").await.unwrap();
        drop(conn);
        here.stop().await.unwrap();
        there_task.await.unwrap();
        println!("exit");
    }
}
