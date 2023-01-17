use matrix_sdk::ruma::serde::Base64;
use sha2::{Digest, Sha512};
use std::fs::File;
use std::io::BufReader;
use std::io::Read;
use std::path::Path;

pub fn file_sha512(file: &Path) -> (Base64, u64) {
    let file = File::open(file).unwrap();
    let mut size = 0u64;
    let mut reader = BufReader::new(file);
    let mut hasher = Sha512::new();

    let mut buffer = [0; 4096];
    while let Ok(bytes_read) = reader.read(&mut buffer) {
        if bytes_read == 0 {
            break;
        }
        size += bytes_read as u64;
        hasher.update(&buffer[..bytes_read]);
    }

    (Base64::new(hasher.finalize().to_vec()), size)
}
