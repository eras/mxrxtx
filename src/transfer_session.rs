use crate::progress_common;
use indicatif::{MultiProgress, ProgressBar, ProgressFinish};

pub struct TransferSession {
    num_transferring: usize,
    num_complete: usize,
    spinner: ProgressBar,
}

impl TransferSession {
    pub fn new(multi_progress: &MultiProgress) -> Self {
        let spinner = progress_common::make_spinner(Some(multi_progress))
            .with_finish(ProgressFinish::AndClear);
        let session = TransferSession {
            num_complete: 0,
            num_transferring: 0,
            spinner,
        };
        session.update_spinner();
        session
    }

    pub fn inc_tranferring(&mut self) {
        self.num_transferring += 1;
        self.update_spinner();
    }

    pub fn inc_complete(&mut self) {
        self.num_complete += 1;
        self.num_transferring -= 1;
        self.update_spinner();
    }

    pub fn update_spinner(&self) {
        self.spinner.set_message(format!(
            "Transfers in progress: {} Complete transfers: {}",
            self.num_transferring, self.num_complete,
        ));
    }
}
