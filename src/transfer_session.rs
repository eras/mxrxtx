use crate::progress_common;
use indicatif::{MultiProgress, ProgressBar, ProgressFinish};

pub struct TransferSession {
    num_transferring: usize,
    num_complete: usize,
    spinner: ProgressBar,
    prefix: String,
}

impl TransferSession {
    pub fn new_from_multiprogess(multi_progress: &MultiProgress, prefix: &str) -> Self {
        let spinner = progress_common::make_spinner(Some(multi_progress))
            .with_finish(ProgressFinish::AndClear);
	Self::new(spinner, prefix)
    }

    pub fn new(spinner: ProgressBar, prefix: &str) -> Self {
        let session = TransferSession {
            num_complete: 0,
            num_transferring: 0,
            spinner,
	    prefix: prefix.to_string(),
        };
        session.update_spinner();
        session
    }

    pub fn inc_tranferring(&mut self) {
        self.num_transferring += 1;
        self.update_spinner();
    }

    pub fn inc_complete(&mut self) -> usize {
        self.num_complete += 1;
        self.num_transferring -= 1;
        self.update_spinner();
        self.num_complete
    }

    pub fn update_spinner(&self) {
        self.spinner.set_message(format!(
            "{}Transfers in progress: {} Complete transfers: {}",
	    self.prefix, self.num_transferring, self.num_complete,
        ));
    }
}
