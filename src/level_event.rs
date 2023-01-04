use async_condvar_fair::{BatonExt, Condvar};
use std::ops::Deref;
use std::sync::Arc;
use tokio::sync::Mutex;

#[derive(Default)]
pub struct LevelEvent {
    level: Arc<Mutex<bool>>,
    cv: Arc<Condvar>,
}

impl LevelEvent {
    pub fn new() -> Self {
        let level = Arc::new(Mutex::new(false));
        let cv = Arc::new(Condvar::new());
        Self { level, cv }
    }

    pub async fn issue(&self) {
        let mut guard = self.level.lock().await;
        *guard = true;
        self.cv.notify_all();
    }

    pub async fn wait(&self) {
        let level = self.level.clone();
        let level = level.as_ref();
        let mut guard = self.level.lock().await;
        let mut baton = None;
        while !guard.deref() {
            baton.dispose();
            (guard, baton) = self.cv.wait_baton((guard, level)).await;
        }
        baton.dispose();
    }
}

impl Clone for LevelEvent {
    fn clone(&self) -> Self {
        LevelEvent {
            level: self.level.clone(),
            cv: self.cv.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::LevelEvent;

    #[tokio::test]
    async fn test_simple() {
        let l = LevelEvent::new();
        l.issue().await;
        l.wait().await;
    }

    #[tokio::test]
    async fn test_spawned() {
        let l = LevelEvent::new();
        let spawned = tokio::spawn({
            let l = l.clone();
            async move {
                l.wait().await;
            }
        });
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        l.issue().await;
        spawned.await.unwrap();
        l.wait().await;
    }

    #[tokio::test]
    async fn test_spawned2() {
        let l = LevelEvent::new();
        let mut handles = vec![];
        handles.push(tokio::spawn({
            let l = l.clone();
            async move {
                l.wait().await;
            }
        }));
        handles.push(tokio::spawn({
            let l = l.clone();
            async move {
                l.wait().await;
            }
        }));
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        l.issue().await;
        futures::future::join_all(handles)
            .await
            .into_iter()
            .map(|x| x.unwrap())
            .for_each(drop);
        l.wait().await;
    }
}
