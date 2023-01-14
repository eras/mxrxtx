use crate::utils::escape;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use std::fmt;
use std::fs;
use std::io;
use std::io::Write;
use std::path::{Path, PathBuf};
use thiserror::Error;

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Default)]
pub struct Config {
    pub user_id: String, // @user_id:server
    pub access_token: String,
    pub device_id: String,
    pub refresh_token: Option<String>,
    pub state_dir: PathBuf,
    pub ice_servers: Vec<String>,
}

#[derive(Error, Debug)]
pub struct ParseError {
    pub filename: String,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Failed to parse {}: {}", self.filename, self.message)
    }
}

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    ParseError(ParseError),

    #[error(transparent)]
    TomlDeError(#[from] toml::de::Error),

    #[error(transparent)]
    TomlSerError(#[from] toml::ser::Error),

    #[error(transparent)]
    IOError(#[from] io::Error),

    #[error(transparent)]
    AtomicIOError(#[from] atomicwrites::Error<io::Error>),

    #[error("Cannot determine default host: {}", .0)]
    DefaultHostError(String),

    #[error(transparent)]
    IdParseError(#[from] matrix_sdk::ruma::IdParseError),
}

pub static FILENAME: &str = "mxrxtx.ini";
pub static STATEDIR: &str = "mxrxtx-state";

impl Config {
    pub fn new() -> Config {
        Config {
            ..Default::default()
        }
    }

    // If no file is found, returns default config instead of error
    pub fn load(filename: &str) -> Result<Config, Error> {
        let contents = match fs::read_to_string(filename) {
            Ok(contents) => contents,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(Config::new()),
            Err(error) => return Err(Error::IOError(error)),
        };
        let config = match toml::from_str(&contents) {
            Ok(contents) => contents,
            Err(error) if error.line_col().is_some() => {
                return Err(Error::ParseError(ParseError {
                    filename: String::from(filename),
                    message: format!("{}", error),
                }));
            }
            Err(error) => return Err(Error::TomlDeError(error)),
        };
        log::debug!("Loaded config from {}", escape(filename));
        Ok(config)
    }

    pub fn save(self, filename: &str) -> Result<(), Error> {
        let mut config_dir = Path::new(filename).to_path_buf();
        config_dir.pop();
        std::fs::create_dir_all(config_dir)?;
        let contents = toml::to_string(&self)?;
        let writer = atomicwrites::AtomicFile::new(filename, atomicwrites::AllowOverwrite);
        writer.write(|f| f.write_all(contents.as_bytes()))?;
        log::debug!("Wrote config to {}", escape(filename));
        Ok(())
    }

    pub fn get_matrix_session(&self) -> Result<matrix_sdk::Session, Error> {
        let user_id = <&matrix_sdk::ruma::UserId>::try_from(self.user_id.as_str())?.to_owned();
        let device_id = <&matrix_sdk::ruma::DeviceId>::try_from(self.device_id.as_str())
            .expect("infallible")
            .to_owned();
        Ok(matrix_sdk::Session {
            access_token: self.access_token.clone(),
            user_id,
            device_id,
            refresh_token: self.refresh_token.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_save() {
        let mut config = Config::new();
        config.user_id = "user_id".to_string();
        config.access_token = "access_token".to_string();
        config.refresh_token = Some("refresh_token".to_string());
        config.save("test.ini").unwrap();
    }
}
