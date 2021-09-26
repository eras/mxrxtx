use directories_next::ProjectDirs;
use mxrxtx::{config, version::get_version, setup, offer, download};
use std::path::Path;

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
        .map_err(|x| log4rs::config::InitError::BuildConfig(x))?;

    log4rs::init_config(config).map_err(|x| log4rs::config::InitError::SetLogger(x))?;

    Ok(())
}

fn get_config_file(config_file_arg: Option<&str>) -> Result<String, Error> {
    let joined_pathbuf;
    let joined_path;
    // argument overrides all automation
    let config_file: &Path = if let Some(config_file) = config_file_arg {
        Path::new(config_file)
    } else {
        let config_file = Path::new(&config::FILENAME);
        // does the default config filename exist? if so, go with that
        let config_file: &Path = if config_file.exists() {
            config_file
        } else {
            // otherwise, choose the XDG directory if it can be created
            (if let Some(proj_dirs) = ProjectDirs::from("", "Erkki Seppälä", "mxrxtx") {
                let config_dir = proj_dirs.config_dir();
                joined_pathbuf = config_dir.join("mxrxtx.ini");
                joined_path = joined_pathbuf.as_path();
                Some(&joined_path)
            } else {
                None
            })
            .unwrap_or(&config_file)
        };
        config_file
    };
    let config_file = if let Some(path) = config_file.to_str() {
        path
    } else {
        return Err(Error::UnsupportedPath(
            "Sorry, unsupported config file path (needs to be legal UTF8)".to_string(),
        ));
    };
    Ok(config_file.to_string())
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    let args = clap::App::new("mxrxtx")
        .setting(clap::AppSettings::ColoredHelp)
	.license("MIT")
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
                .about(
                    format!(
                        "Config file to load, defaults to {}",
                        get_config_file(None)?
                    )
                    .as_str(),
                ),
        )
        .arg(
            clap::Arg::new("debug")
                .long("debug")
                .about(&format!("Enable debug logging to {}", DEBUG_LOG_FILE)),
        )
        .arg(
            clap::Arg::new("setup")
                .long("setup")
                .about("Do setup (prompt matrix homeserver address, user account, password, TODO: setup e2ee)"),
        )
        .arg(
            clap::Arg::new("download")
                .short('d')
                .long("download")
                .takes_value(true)
                .multiple_values(true)
                .min_values(1)
                .about("Download files offered by a given Matrix event, given as a matrix: or https://matrix.to url"),
        )
        .arg(
            clap::Arg::new("offer")
                .short('o')
                .long("offer")
                .takes_value(true)
                .multiple_values(true)
                .min_values(2)
                .about("Offer the list of files provided after room pointer by the first argument; the following arguments are the local file names."),
        )
	.group(clap::ArgGroup::new("mode")
               .args(&["offer", "download", "setup"])
               .required(true))
        .get_matches();

    init_logging(args.is_present("debug"))?;

    let config_file = get_config_file(args.value_of("config"))?;
    let config = config::Config::load(&config_file)?;

    if args.is_present("setup") {
	setup::setup_mode(args, config, &config_file).await?
    } else if args.is_present("download") {
	let args: Vec<String> = args.values_of_t("download").expect("clap arguments should ensure this");
	let urls: Vec<&str> = args.iter().map(|x| x.as_str()).collect();
	download::download(config, urls).await?;
    } else if args.is_present("offer") {
	let args: Vec<String> = args.values_of_t("offer").expect("clap arguments should ensure this");
	let room = &args[0];
	let files: Vec<&str> = args[1..args.len()].iter().map(|x| x.as_str()).collect();
	println!("files: {:?}", files);
	offer::offer(config, room, files).await?;
    } else {
	panic!("Clap group should ensure at least one of these is set..");
    }

    Ok(())
}
