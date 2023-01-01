use std::io::{stdin, stdout, Write};
use termion::input::TermRead;

use crate::config;

use std::convert::TryFrom;

use thiserror::Error;

use matrix_sdk::Client;

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    ConfigError(#[from] config::Error),

    #[error(transparent)]
    IOError(#[from] std::io::Error),

    #[error("No input was provided")]
    NoInputError,

    #[error("Failure to setup: {}", .0)]
    SetupError(String),

    #[error(transparent)]
    RumaError(#[from] matrix_sdk::Error),

    #[error(transparent)]
    RumaIdentifierError(#[from] ruma_identifiers::Error),

    #[error(transparent)]
    MatrixClientbuildError(#[from] matrix_sdk::ClientBuildError),

    #[error(transparent)]
    IdParseError(#[from] ruma::IdParseError),
}

pub async fn setup_mode(
    _args: clap::ArgMatches,
    mut config: config::Config,
    config_file: &str,
) -> Result<(), Error> {
    let join = tokio::task::spawn_blocking({
        move || {
            let stdout = stdout();
            let mut stdout = stdout.lock();
            let stdin = stdin();
            let mut stdin = stdin.lock();

            stdout.write_all(b"Matrix id (e.g. @user:example.org): ")?;
            stdout.flush()?;
            let mxid = stdin.read_line()?.ok_or(Error::NoInputError)?;

            stdout.write_all(b"Device name (empty to use default device name \"mxrxtx\"): ")?;
            stdout.flush()?;
            let device_name = stdin.read_line()?.ok_or(Error::NoInputError)?;
            let device_name = if device_name.is_empty() {
                None
            } else {
                Some(device_name)
            };

            stdout.write_all(b"Password: ")?;
            stdout.flush()?;
            let password = stdin.read_passwd(&mut stdout)?.ok_or(Error::NoInputError)?;
            stdout.write_all(b"\n")?;

            Ok((mxid, password, device_name))
        }
    });
    let (mxid, password, device_name) = match join.await {
        Ok(Ok(x)) => x,
        Ok(Err(x)) => return Err(x),
        Err(_) => return Err(Error::SetupError(String::from("Failed to wait setup"))),
    };
    let user_id = <&ruma::UserId>::try_from(mxid.as_str())?.to_owned();

    let client = Client::builder()
        .server_name(user_id.server_name())
        .build()
        .await?;

    let login = client
        .login_username(user_id.localpart(), &password)
        .device_id(&device_name.unwrap_or_else(|| "mxrxtx".to_string()))
        .send()
        .await?;

    config.user_id = user_id.to_string();
    config.access_token = login.access_token;
    config.refresh_token = login.refresh_token;
    config.device_id = login.device_id.to_string();
    config.save(config_file)?;

    println!("Login successful. Saved configuration to {}", config_file);

    Ok(())
}
