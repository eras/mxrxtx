use async_condvar_fair::{BatonExt, Condvar};
use std::ops::Deref;
use tokio::sync::Mutex;

pub struct LevelEvent {
    level: Mutex<bool>,
    cv: Condvar,
}

impl LevelEvent {
    pub fn new() -> Self {
        let level = Mutex::new(false);
        let cv = Condvar::new();
        Self { level, cv }
    }

    pub async fn issue(&self) {
        let mut guard = self.level.lock().await;
        *guard = true;
        self.cv.notify_all();
    }

    pub async fn wait(&self) {
        let mut guard = self.level.lock().await;
        let mut baton = None;
        while !guard.deref() {
            baton.dispose();
            (guard, baton) = self.cv.wait_baton((guard, &self.level)).await;
        }
        baton.dispose();
    }
}
