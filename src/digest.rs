use crate::progress_common;
use indicatif::MultiProgress;
use matrix_sdk::ruma::serde::Base64;
use sha2::{Digest, Sha512};
use std::fs::File;
use std::io::BufReader;
use std::io::Read;
use std::path::Path;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    IoError(#[from] std::io::Error),
}

pub fn file_sha512(file: &Path, multi: Option<&MultiProgress>) -> Result<(Base64, u64), Error> {
    let file = File::open(file).unwrap();
    let file_size = file.metadata()?.len();
    let progress = progress_common::make_transfer_progress(file_size, multi);
    let mut size = 0u64;
    let mut reader = BufReader::new(file);
    let mut hasher = Sha512::new();

    let mut buffer = [0; 4096];
    while let Ok(bytes_read) = reader.read(&mut buffer) {
        progress.inc(bytes_read as u64);
        if bytes_read == 0 {
            break;
        }
        size += bytes_read as u64;
        hasher.update(&buffer[..bytes_read]);
    }

    Ok((Base64::new(hasher.finalize().to_vec()), size))
}
