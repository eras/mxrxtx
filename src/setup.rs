use crate::{
    config, console, matrix_common,
    utils::{escape, escape_paths},
};
use directories_next::ProjectDirs;
use matrix_sdk::ruma::api::client::session::{
    get_login_types::v3::{IdentityProvider, LoginType},
    login::v3::Response as LoginResponse,
};
use matrix_sdk::ruma::{OwnedDeviceId, OwnedUserId};
use matrix_sdk::Client;
use rand::distributions::{Alphanumeric, DistString};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use thiserror::Error;
use tokio::sync::mpsc;
use tokio::sync::Mutex;

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
    MatrixSdkError(#[from] matrix_sdk::Error),

    #[error(transparent)]
    MatrixSdkHttpError(#[from] matrix_sdk::HttpError),

    #[error(transparent)]
    MatrixClientbuildError(#[from] matrix_sdk::ClientBuildError),

    #[error(transparent)]
    IdParseError(#[from] matrix_sdk::ruma::IdParseError),

    #[error("Failure to process path: {}", .0)]
    UnsupportedPath(String),

    #[error("No login methods available")]
    NoLoginMethodsAvailable,

    #[error("Unsupported login method")]
    UnsupportedLoginMethod,

    #[error("No identity provider available")]
    NoIdentityProvidersAvailable,

    #[error(transparent)]
    ConsoleError(#[from] console::Error),

    #[error(transparent)]
    MatrixVerifyError(#[from] crate::matrix_verify::Error),

    #[error(transparent)]
    MatrixCommonError(#[from] matrix_common::Error),

    #[error(transparent)]
    ParseIntError(#[from] std::num::ParseIntError),

    #[error(transparent)]
    JoinError(#[from] tokio::task::JoinError),
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

async fn prompt_device_name() -> Result<String, Error> {
    let device_name =
        console::prompt("Device display name (empty to use default device name \"mxrxtx\"):")
            .await?;
    if device_name.is_empty() {
        Ok("mxrxtx".to_string())
    } else {
        Ok(device_name)
    }
}

async fn prompt_device_id() -> Result<Option<String>, Error> {
    let device_id =
        console::prompt("Device id (empty to use default automatically generated id):").await?;
    if device_id.is_empty() {
        Ok(None)
    } else {
        Ok(Some(device_id))
    }
}

async fn prompt_password() -> Result<String, Error> {
    console::print("Password: ").await?;
    let password = console::read_passwd().await?;
    console::print("\n").await?;
    Ok(password)
}

async fn prompt_state_dir(device_id: &OwnedDeviceId) -> Result<PathBuf, Error> {
    let default_state_dir = project_dir()
        .map(|project_dir| {
            let mut path = project_dir.cache_dir().to_path_buf();
            path.push(escape_paths(device_id.as_ref()));
            path
        })
        .unwrap_or_else(|| Path::new(&escape_paths(device_id.as_ref())).to_path_buf());
    let state_dir = console::prompt(&format!(
        "State directory (empty to use default state directory \"{}\"):",
        escape(&default_state_dir.to_string_lossy())
    ))
    .await?;
    if let Some(parent) = Path::new(&state_dir).parent() {
        std::fs::create_dir_all(parent)?;
    }
    let state_dir = if state_dir.is_empty() {
        default_state_dir
    } else {
        Path::new(&state_dir).to_path_buf()
    };
    Ok(state_dir)
}

async fn prompt_ice_servers() -> Result<Vec<String>, Error> {
    let default_ice_servers = DEFAULT_ICE_SERVERS.join(", ");
    let ice_servers = console::prompt(&format!(
                    "List stun/turn servers in a comma separated list (empty to use {default_ice_servers}; use - for no stun/turn servers):"
	    )).await?;
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
    Ok(ice_servers)
}

async fn prompt_log_room(config: &config::Config) -> Result<Option<String>, Error> {
    let log_room = console::prompt(
        "Which room (can be #alias:hs, !id or name) to use for sending log messages, or none?",
    )
    .await?;
    if !log_room.is_empty() {
        // create a new client with loaded data and state
        let session = config.get_matrix_session()?;
        let user_id = <&matrix_sdk::ruma::UserId>::try_from(config.user_id.as_str())?.to_owned();
        let client = Client::builder()
            .server_name(user_id.server_name())
            .build()
            .await?;
        client.restore_session(session).await?;

        let log_room = matrix_common::get_joined_room_by_name(&client, &log_room).await?;

        Ok(Some(log_room.room_id().to_string()))
    } else {
        Ok(None)
    }
}

pub async fn prompt_flow(flows: &[LoginType]) -> Result<LoginType, Error> {
    console::print("The following login flows are available:\n").await?;
    for (index, flow) in flows.iter().enumerate() {
        console::print(&format!("  {index}: {flow:?}\n", index = index + 1)).await?;
    }
    let selection: usize = console::prompt("Select a flow by its number:")
        .await?
        .parse()?;
    if selection >= 1 && selection <= flows.len() {
        Ok(flows[selection - 1].clone())
    } else {
        Err(Error::NoLoginMethodsAvailable)
    }
}

pub async fn prompt_identity_provider(
    providers: &[IdentityProvider],
) -> Result<IdentityProvider, Error> {
    console::print("The following identity providers are available:\n").await?;
    for (index, flow) in providers.iter().enumerate() {
        console::print(&format!("  {index}: {flow:?}\n", index = index + 1)).await?;
    }
    let selection: usize = console::prompt("Select a provider by its number:")
        .await?
        .parse()?;
    if selection >= 1 && selection <= providers.len() {
        Ok(providers[selection - 1].clone())
    } else {
        Err(Error::NoIdentityProvidersAvailable)
    }
}

pub async fn make_login(client: &Client, user_id: &OwnedUserId) -> Result<LoginResponse, Error> {
    let device_name = prompt_device_name().await?;
    let device_id = prompt_device_id().await?;

    let methods = client.get_login_types().await?;
    let login_flow: LoginType = match &methods
        .flows
        .iter()
        .filter(|login_type| matches!(login_type, LoginType::Password(_) | LoginType::Sso(_)))
        .cloned()
        .collect::<Vec<_>>()[..]
    {
        [] => {
            error!("Homeserver provided no login types; cannot setup");
            return Err(Error::NoLoginMethodsAvailable);
        }
        [flow] => flow.clone(),
        flows @ [_, _, ..] => prompt_flow(flows).await?,
    };
    let login = match login_flow {
        LoginType::Password(_) => {
            let password = prompt_password().await?;
            info!("Logging in");
            client.login_username(user_id.localpart(), &password)
        }
        LoginType::Sso(_sso) => {
            // TODO: actually use Some(provider_id) once the quoting bug issue is fixed:
            // https://github.com/ruma/ruma/issues/1447
            // let provider_id = (match &sso.identity_providers[..] {
            //     [] => {
            //         error!("Homeserver provided no login types; cannot setup");
            //         return Err(Error::NoIdentityProvidersAvailable);
            //     }
            //     [provider] => provider.clone(),
            //     providers @ [_, _, ..] => prompt_identity_provider(providers).await?,
            // })
            // .id;
            use warp::Filter;
            let (response_send, mut response_recv) = mpsc::channel(1);
            let response_send = Arc::new(Mutex::new(response_send));
            let prefix = Alphanumeric.sample_string(&mut rand::thread_rng(), 16);

            // http://127.0.0.1:46005/?loginToken=token
            let routes = warp::get()
                .and(warp::path(prefix.clone()))
                .and(warp::query::<HashMap<String, String>>())
                //.and_then(diipadaipa);
                .and_then(move |query: HashMap<String, String>| {
                    let response_send = response_send.clone();
                    let login_token = query.get("loginToken").cloned();
                    async move {
                        if let Some(login_token) = login_token {
                            // TODO: handle errors properly
                            response_send.lock().await.send(login_token).await.unwrap();
                        }
                        Ok::<_, std::convert::Infallible>(
                            "You may now proceed with the setup.".to_string(),
                        )
                    }
                });
            let (addr, warp) = warp::serve(routes).bind_ephemeral(([127, 0, 0, 1], 0));
            let warp_join = tokio::spawn(warp);
            let url = format!("http://{addr}/{prefix}");
            info!("Started SSO response server at {url}");
            let url = client.get_sso_login_url(&url, None).await?;
            console::print(&format!(
                "\nPlease visit\n\n  {url}\n\n\
		 Note that your browser (or extension like NoScript) may prevent you from\n\
                 landing to the web server running locally for this authentication, in\n\
		 which case you may need to copy&paste the link from the final login\n\
		 button to your browser URL field.\n"
            ))
            .await?;
            // TODO: handle errors properly
            let token = response_recv.recv().await.unwrap();
            info!("Received token! Logging in.");
            drop(warp_join);
            client.login_token(&token)
        }
        _ => return Err(Error::UnsupportedLoginMethod),
    };

    let login = login.initial_device_display_name(&device_name);
    let login = match &device_id {
        Some(device_id) => login.device_id(device_id),
        None => login,
    };
    let login = login.send().await?;

    Ok(login)
}

pub async fn setup_mode(
    _args: clap::ArgMatches,
    mut config: config::Config,
    config_file: &str,
) -> Result<(), Error> {
    if std::path::Path::new(config_file).exists() {
        return Err(Error::SetupError(format!(
            "Config file {config_file} already exists, not running setup.\n"
        )));
    }

    let mxid = console::prompt("Matrix id (e.g. @user:example.org):").await?;

    let user_id = <&matrix_sdk::ruma::UserId>::try_from(mxid.as_str())?.to_owned();

    let client = Client::builder()
        .server_name(user_id.server_name())
        .build()
        .await?;

    let login = make_login(&client, &user_id).await?;
    let device_id = login.device_id.clone();

    let state_dir = prompt_state_dir(&device_id).await?;

    let ice_servers = prompt_ice_servers().await?;

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

    drop(client);
    match prompt_log_room(&config).await {
        Ok(Some(log_room)) => {
            config.log_room = Some(log_room);
            config.save(config_file)?;
            info!("Saved configuration");
        }
        Ok(None) => (),
        Err(err) => {
            error!(
                "There was an error: {err:?}. Continuing with emoji verification anyway.\n\
		 You can edit the configuration to enable the log room."
            );
        }
    }

    info!(
        "Starting emoji verification. Press ^C to skip. \
	 You may restart verification later with mxrxtx verify."
    );
    crate::matrix_verify::verify(config).await?;

    Ok(())
}
