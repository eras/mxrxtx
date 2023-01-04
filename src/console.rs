use std::io::{BufRead, StdinLock, StdoutLock};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    IOError(#[from] std::io::Error),

    #[error("No input was provided")]
    NoInputError,
}

#[cfg(not(target_os = "windows"))]
pub fn read_passwd(
    stdin: &mut StdinLock,
    stdout: &mut StdoutLock,
) -> Result<Option<String>, Error> {
    use termion::input::TermRead;
    stdin.read_passwd(stdout).map_err(|_| Error::NoInputError)
}

#[cfg(target_os = "windows")]
pub fn read_passwd(
    stdin: &mut StdinLock,
    _stdout: &mut StdoutLock,
) -> Result<Option<String>, Error> {
    read_line(stdin)
}

pub fn read_line(stdin: &mut StdinLock) -> Result<Option<String>, Error> {
    let mut buffer = String::new();
    BufRead::read_line(stdin, &mut buffer)?;
    Ok(Some(buffer.trim_end().to_string()))
}
