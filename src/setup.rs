use crate::config;
use directories_next::ProjectDirs;
use matrix_sdk::Client;
use std::convert::TryFrom;
use std::io::{stdin, stdout, Write};
use std::path::{Path, PathBuf};
use thiserror::Error;

#[allow(unused_imports)]
use log::{debug, error, info, warn};

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

    #[error("Failure to process path: {}", .0)]
    UnsupportedPath(String),
}

fn project_dir() -> Option<ProjectDirs> {
    ProjectDirs::from("", "Erkki Seppälä", "mxrxtx")
}

fn get_path_logic<SelectPathFn>(
    path_arg: Option<&str>,
    select_path: SelectPathFn,
) -> Result<String, Error>
where
    SelectPathFn: Fn(&ProjectDirs) -> PathBuf,
{
    let joined_pathbuf;
    let joined_path;
    // argument overrides all automation
    let path: &Path = if let Some(path) = path_arg {
        Path::new(path)
    } else {
        let path = Path::new(&config::FILENAME);
        // does the default config filename exist? if so, go with that
        let path: &Path = if path.exists() {
            path
        } else {
            // otherwise, choose the XDG directory if it can be created
            (if let Some(proj_dirs) = project_dir() {
                joined_pathbuf = select_path(&proj_dirs);
                joined_path = joined_pathbuf.as_path();
                Some(&joined_path)
            } else {
                None
            })
            .unwrap_or(&path)
        };
        path
    };
    let path = if let Some(path) = path.to_str() {
        path
    } else {
        return Err(Error::UnsupportedPath(
            "Sorry, unsupported config file path (needs to be legal UTF8)".to_string(),
        ));
    };
    Ok(path.to_string())
}

pub fn get_config_file(config_file_arg: Option<&str>) -> Result<String, Error> {
    get_path_logic(config_file_arg, |project_dirs| {
        project_dirs.config_dir().join("mxrxtx.ini")
    })
}

// Termion that provides read_passwd doesn't compile on Windows
mod console {
    use std::io::{BufRead, StdinLock, StdoutLock};

    #[cfg(not(target_os = "windows"))]
    pub fn read_passwd(
        stdin: &mut StdinLock,
        stdout: &mut StdoutLock,
    ) -> Result<Option<String>, super::Error> {
        use termion::input::TermRead;
        stdin
            .read_passwd(stdout)
            .map_err(|_| super::Error::NoInputError)
    }

    #[cfg(target_os = "windows")]
    pub fn read_passwd(
        stdin: &mut StdinLock,
        _stdout: &mut StdoutLock,
    ) -> Result<Option<String>, super::Error> {
        read_line(stdin)
    }

    pub fn read_line(stdin: &mut StdinLock) -> Result<Option<String>, super::Error> {
        let mut buffer = String::new();
        BufRead::read_line(stdin, &mut buffer)?;
        Ok(Some(buffer.trim_end().to_string()))
    }
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

            let mxid = {
                stdout.write_all(b"Matrix id (e.g. @user:example.org): ")?;
                stdout.flush()?;
                console::read_line(&mut stdin)?.ok_or(Error::NoInputError)?
            };

            stdout.write_all(
                b"Device display name (empty to use default device name \"mxrxtx\"): ",
            )?;
            stdout.flush()?;
            let device_name = console::read_line(&mut stdin)?.ok_or(Error::NoInputError)?;
            let device_name = if device_name.is_empty() {
                "mxrxtx".to_string()
            } else {
                device_name
            };

            stdout.write_all(b"Device id (empty to use default automatically generated id): ")?;
            stdout.flush()?;
            let device_id = console::read_line(&mut stdin)?.ok_or(Error::NoInputError)?;
            let device_id = if device_id.is_empty() {
                None
            } else {
                Some(device_id)
            };

            stdout.write_all(b"Password: ")?;
            stdout.flush()?;
            let password =
                console::read_passwd(&mut stdin, &mut stdout)?.ok_or(Error::NoInputError)?;
            stdout.write_all(b"\n")?;

            Ok((mxid, password, device_id, device_name))
        }
    });
    let (mxid, password, device_id, device_name) = match join.await {
        Ok(Ok(x)) => x,
        Ok(Err(x)) => return Err(x),
        Err(_) => return Err(Error::SetupError(String::from("Failed to wait setup"))),
    };
    let user_id = <&ruma::UserId>::try_from(mxid.as_str())?.to_owned();

    let client = Client::builder()
        .server_name(user_id.server_name())
        .build()
        .await?;

    info!("Logging in");
    let login = client
        .login_username(user_id.localpart(), &password)
        .initial_device_display_name(&device_name);
    let login = match &device_id {
        Some(device_id) => login.device_id(device_id),
        None => login,
    };
    let login = login.send().await?;

    let join = tokio::task::spawn_blocking({
        move || {
            let stdout = stdout();
            let mut stdout = stdout.lock();
            let stdin = stdin();
            let mut stdin = stdin.lock();

            let default_state_dir = project_dir()
                .map(|project_dir| project_dir.cache_dir().to_path_buf())
                .unwrap_or_else(|| Path::new(".").to_path_buf());
            stdout.write_all(
                format!(
                    "State directory (empty to use default state directory \"{}\"): ",
                    default_state_dir.to_string_lossy()
                )
                .as_bytes(),
            )?;
            stdout.flush()?;
            let state_dir = console::read_line(&mut stdin)?.ok_or(Error::NoInputError)?;
            let state_dir = if state_dir.is_empty() {
                default_state_dir
            } else {
                Path::new(&state_dir).to_path_buf()
            };

            Ok(state_dir)
        }
    });
    let state_dir = match join.await {
        Ok(Ok(x)) => x,
        Ok(Err(x)) => return Err(x),
        Err(_) => return Err(Error::SetupError(String::from("Failed to wait setup"))),
    };

    config.user_id = user_id.to_string();
    config.access_token = login.access_token;
    config.refresh_token = login.refresh_token;
    config.device_id = login.device_id.to_string();
    config.state_dir = state_dir;
    config.save(config_file)?;

    info!("Login successful. Saved configuration to {}", config_file);

    Ok(())
}
