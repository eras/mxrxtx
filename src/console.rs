use std::io::{stdin, stdout, BufRead, Write};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    IOError(#[from] std::io::Error),

    #[error("No input was provided")]
    NoInputError,

    #[error(transparent)]
    JoinError(#[from] tokio::task::JoinError),
}

#[cfg(not(target_os = "windows"))]
pub async fn read_passwd() -> Result<String, Error> {
    tokio::task::spawn_blocking(|| {
        use termion::input::TermRead;
        let stdin = stdin();
        let stdout = stdout();
        let mut stdin = stdin.lock();
        let mut stdout = stdout.lock();
        match stdin.read_passwd(&mut stdout) {
            Ok(Some(x)) => Ok(x),
            _ => Err(Error::NoInputError),
        }
    })
    .await?
}

#[cfg(target_os = "windows")]
pub async fn read_passwd() -> Result<String, Error> {
    read_line().await
}

pub async fn read_line() -> Result<String, Error> {
    tokio::task::spawn_blocking(|| {
        let mut buffer = String::new();
        let stdin = stdin();
        let mut stdin = stdin.lock();
        BufRead::read_line(&mut stdin, &mut buffer)?;
        Ok(buffer.trim_end().to_string())
    })
    .await?
}

pub async fn print(message: &str) -> Result<(), Error> {
    let message = message.to_string();
    tokio::task::spawn_blocking(move || {
        let stdout = stdout();
        let mut stdout = stdout.lock();
        stdout.write_all(message.as_bytes())?;
        stdout.flush()?;
        Ok(())
    })
    .await?
}

pub async fn prompt(message: &str) -> Result<String, Error> {
    print(message).await?;
    print(" ").await?;
    read_line().await
}
