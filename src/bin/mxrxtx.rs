use directories_next::ProjectDirs;
use mxrxtx::{config, download, offer, setup, version::get_version};
use std::path::{Path, PathBuf};

use thiserror::Error;

const DEBUG_LOG_FILE: &str = "mxrxtx.log";

#[derive(Error, Debug)]
pub enum LoggingSetupError {
    #[error(transparent)]
    InitLoggingError(#[from] log4rs::config::InitError),

    #[error(transparent)]
    LogFileOpenError(#[from] std::io::Error),
}

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    LoggingSetupError(#[from] LoggingSetupError),

    #[error("Failure to process path: {}", .0)]
    UnsupportedPath(String),

    #[error(transparent)]
    ConfigError(#[from] config::Error),

    #[error(transparent)]
    IOError(#[from] std::io::Error),

    #[error(transparent)]
    SetupError(#[from] setup::Error),

    #[error(transparent)]
    OfferError(#[from] offer::Error),

    #[error(transparent)]
    DownloadError(#[from] download::Error),
}

fn init_logging(enable: bool) -> Result<(), LoggingSetupError> {
    if !enable {
        return Ok(());
    }
    use log::LevelFilter;
    use log4rs::append::file::FileAppender;
    use log4rs::config::{Appender, Config, Root};
    use log4rs::encode::pattern::PatternEncoder;

    let logfile = FileAppender::builder()
        .encoder(Box::new(PatternEncoder::new("{d} {l} {M} {m}\n")))
        .build(DEBUG_LOG_FILE)?;

    let config = Config::builder()
        .appender(Appender::builder().build("logfile", Box::new(logfile)))
        .build(
            Root::builder()
                .appender("logfile")
                .build(LevelFilter::Debug),
        )
        .map_err(log4rs::config::InitError::BuildConfig)?;

    log4rs::init_config(config).map_err(log4rs::config::InitError::SetLogger)?;

    Ok(())
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

fn get_config_file(config_file_arg: Option<&str>) -> Result<String, Error> {
    get_path_logic(config_file_arg, |project_dirs| {
        project_dirs.config_dir().join("mxrxtx.ini")
    })
}

fn get_state_dir(state_dir_arg: Option<&str>) -> Result<String, Error> {
    get_path_logic(state_dir_arg, |project_dirs| {
        project_dirs.cache_dir().into()
    })
}

// fn get_state_dir(state_dir_arg: Option<&str>) -> Result<String, Error> {
//     // The location to save files to
//     let home = dirs::home_dir()
//         .expect("no home directory found")
//         .join("party_bot");
//     client_builder = client_builder.sled_store(home, None)?;
// }

#[tokio::main]
async fn main() -> Result<(), Error> {
    let args = clap::App::new("mxrxtx")
        .setting(clap::AppSettings::ColoredHelp)
	.before_help("Licensed under the MIT license")
        .version(get_version().as_str())
        .author("Erkki Seppälä <erkki.seppala@vincit.fi>")
        .about("Transfer files over Matrix, directly from client to client with WebRTC.

Licensed under the MIT license; refer to LICENSE.MIT for details.
")
        .arg(
            clap::Arg::new("config")
                .long("config")
                .short('c')
                .takes_value(true)
                .help(
                    format!(
                        "Config file to load, defaults to {}",
                        get_config_file(None)?
                    )
                    .as_str(),
                ),
        )
        .arg(
            clap::Arg::new("output-dir")
                .long("output")
                .short('O')
                .default_value(".")
                .help(
                    "Directory to use for downloading, defaults to ."
                ),
        )
        .arg(
            clap::Arg::new("state")
                .long("state")
                .takes_value(true)
                .help(
                    format!(
                        "State directory to use, defaults to {}",
                        get_state_dir(None)?
                    )
                    .as_str(),
                ),
        )
        .arg(
            clap::Arg::new("debug")
                .long("debug")
		.help(format!("Enable debug logging to {}", DEBUG_LOG_FILE).as_str()),
        )
        .arg(
            clap::Arg::new("setup")
                .long("setup")
                .help("Do setup (prompt matrix homeserver address, user account, password, TODO: setup e2ee)"),
        )
        .arg(
            clap::Arg::new("download")
                .short('d')
                .long("download")
                .takes_value(true)
                .multiple_values(true)
                .min_values(1)
                .help("Download files offered by a given Matrix event, given as a matrix: or https://matrix.to url"),
        )
        .arg(
            clap::Arg::new("offer")
                .short('o')
                .long("offer")
                .takes_value(true)
                .multiple_values(true)
                .min_values(2)
                .help("Offer the list of files provided after room pointer by the first argument; the following arguments are the local file names."),
        )
	.group(clap::ArgGroup::new("mode")
               .args(&["offer", "download", "setup"])
               .required(true))
        .get_matches();

    init_logging(args.is_present("debug"))?;

    let config_file = get_config_file(args.value_of("config"))?;
    let config = config::Config::load(&config_file)?;

    let state_dir = get_state_dir(args.value_of("state"))?;

    let output_dir = args.value_of("output-dir").unwrap();

    if args.is_present("setup") {
        setup::setup_mode(args, config, &config_file).await?
    } else if args.is_present("download") {
        let args: Vec<String> = args
            .values_of_t("download")
            .expect("clap arguments should ensure this");
        let urls: Vec<&str> = args.iter().map(|x| x.as_str()).collect();
        download::download(config, &state_dir, urls, output_dir).await?;
    } else if args.is_present("offer") {
        let args: Vec<String> = args
            .values_of_t("offer")
            .expect("clap arguments should ensure this");
        let room = &args[0];
        let files: Vec<&str> = args[1..args.len()].iter().map(|x| x.as_str()).collect();
        println!("files: {:?}", files);
        offer::offer(config, &state_dir, room, files).await?;
    } else {
        panic!("Clap group should ensure at least one of these is set..");
    }

    Ok(())
}
