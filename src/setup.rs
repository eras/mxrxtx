use crate::{
    config, console,
    utils::{escape, escape_paths},
};
use directories_next::ProjectDirs;
use matrix_sdk::Client;
use std::convert::TryFrom;
use std::path::{Path, PathBuf};
use thiserror::Error;

#[allow(unused_imports)]
use log::{debug, error, info, warn};

const DEFAULT_ICE_SERVERS: &[&str] = &["stun:stun.l.google.com:19302"];

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
    MatrixClientbuildError(#[from] matrix_sdk::ClientBuildError),

    #[error(transparent)]
    IdParseError(#[from] matrix_sdk::ruma::IdParseError),

    #[error("Failure to process path: {}", .0)]
    UnsupportedPath(String),

    #[error(transparent)]
    ConsoleError(#[from] console::Error),

    #[error(transparent)]
    MatrixVerifyError(#[from] crate::matrix_verify::Error),
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

pub async fn setup_mode(
    _args: clap::ArgMatches,
    mut config: config::Config,
    config_file: &str,
) -> Result<(), Error> {
    let mxid = {
        console::print("Matrix id (e.g. @user:example.org): ").await?;
        console::read_line().await?.ok_or(Error::NoInputError)?
    };

    console::print("Device display name (empty to use default device name \"mxrxtx\"): ").await?;
    let device_name = console::read_line().await?.ok_or(Error::NoInputError)?;
    let device_name = if device_name.is_empty() {
        "mxrxtx".to_string()
    } else {
        device_name
    };

    console::print("Device id (empty to use default automatically generated id): ").await?;
    let device_id = console::read_line().await?.ok_or(Error::NoInputError)?;
    let device_id = if device_id.is_empty() {
        None
    } else {
        Some(device_id)
    };

    console::print("Password: ").await?;
    let password = console::read_passwd().await?.ok_or(Error::NoInputError)?;
    console::print("\n").await?;
    let user_id = <&matrix_sdk::ruma::UserId>::try_from(mxid.as_str())?.to_owned();

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
    let device_id = login.device_id.clone();

    let default_state_dir = project_dir()
        .map(|project_dir| {
            let mut path = project_dir.cache_dir().to_path_buf();
            path.push(escape_paths(device_id.as_ref()));
            path
        })
        .unwrap_or_else(|| Path::new(&escape_paths(device_id.as_ref())).to_path_buf());
    console::print(&format!(
        "State directory (empty to use default state directory \"{}\"): ",
        escape(&default_state_dir.to_string_lossy())
    ))
    .await?;
    let state_dir = console::read_line().await?.ok_or(Error::NoInputError)?;
    if let Some(parent) = Path::new(&state_dir).parent() {
        std::fs::create_dir_all(parent)?;
    }
    let state_dir = if state_dir.is_empty() {
        default_state_dir
    } else {
        Path::new(&state_dir).to_path_buf()
    };

    let default_ice_servers = DEFAULT_ICE_SERVERS.join(", ");
    console::print(&format!(
                    "List stun/turn servers in a comma separated list (empty to use {default_ice_servers}; use - for no stun/turn servers): "
	    )).await?;
    let ice_servers = console::read_line().await?.ok_or(Error::NoInputError)?;
    let ice_servers = if ice_servers.is_empty() {
        default_ice_servers
    } else if &ice_servers == "-" {
        "".to_string()
    } else {
        ice_servers
    };
    let ice_servers: Vec<String> = ice_servers
        .split(',')
        .map(|s| s.trim().to_string())
        .collect();

    config.user_id = user_id.to_string();
    config.access_token = login.access_token;
    config.refresh_token = login.refresh_token;
    config.device_id = login.device_id.to_string();
    config.state_dir = state_dir;
    config.ice_servers = ice_servers;
    config.save(config_file)?;

    info!(
        "Login successful. Saved configuration to {}",
        escape(config_file)
    );

    info!("Starting emoji verification. Press ^C to skip.");
    crate::matrix_verify::verify(config).await?;

    Ok(())
}
