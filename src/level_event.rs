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
