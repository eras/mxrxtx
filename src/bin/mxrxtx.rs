use mxrxtx::{config, download, matrix_verify, monitor, offer, setup, version::get_version};
use thiserror::Error;
use std::path::Path;
use std::fs::File;

#[derive(Error, Debug)]
pub enum Error {
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

    #[error(transparent)]
    VerifyError(#[from] matrix_verify::Error),

    #[error(transparent)]
    MonitorError(#[from] monitor::Error),

    #[error(transparent)]
    ParseIntError(#[from] std::num::ParseIntError),

    #[error(transparent)]
    TracingSubscriberFilterParseError(#[from] tracing_subscriber::filter::ParseError),
}

const DEFAULT_LOG_FILTER: &str = "mxrxtx=trace";

fn init_logging(log_file_name: Option<&str>) -> Result<Option<tracing_appender::non_blocking::WorkerGuard>, Error> {
    let log_file_path = if let Some(log_file_name) = log_file_name {
	Path::new(log_file_name)
    } else {
	return Ok(None)
    };

    let log_file = File::create(log_file_path)?;

    let format = tracing_subscriber::fmt::format()
	.with_level(true)
	.with_target(false)
	.with_thread_ids(true)
	.with_thread_names(true)
	.with_source_location(true)
	.compact();

    let env_filter = tracing_subscriber::EnvFilter::builder()
	.with_default_directive(DEFAULT_LOG_FILTER.parse()?)
	.from_env_lossy();

    let (non_blocking, guard) = tracing_appender::non_blocking(log_file);
    let subscriber = tracing_subscriber::fmt::Layer::new()
	.event_format(format)
	.with_writer(non_blocking);

    use tracing_subscriber::prelude::*;
    tracing_subscriber::registry()
	.with(subscriber.with_ansi(false))
	.with(env_filter)
	.init();

    Ok(Some(guard))
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    let version = get_version();
    let config_help = format!(
        "Config file to load, defaults to {}",
        setup::get_config_file(None)?
    );
    let debug_help =
	format!("Enable logging according to RUST_LOG to given file (default: {DEFAULT_LOG_FILTER}). \
                 The file will always be overwritten.");
    let app = clap::App::new("mxrxtx")
        .setting(clap::AppSettings::ColoredHelp)
        .setting(clap::AppSettings::ArgRequiredElseHelp)
        .version(version.as_str())
        .author("Erkki Seppälä <erkki.seppala@vincit.fi>")
        .about(
            "Transfer files over Matrix, directly from client to client with WebRTC. \n\
             Visit https://github.com/eras/mxrxrx/ or #mxrxtx:matrix.org for more info!\n\
	     \n\
	     Licensed under the MIT license; refer to LICENSE.MIT for details.",
        )
        .arg(
            clap::Arg::new("config")
                .long("config")
                .short('c')
                .takes_value(true)
                .value_name("FILE")
                .help(config_help.as_str()),
        )
        .subcommand(
            clap::Command::new("setup")
                .about("Run the initial setup")
                .arg(
                    clap::Arg::new("homeserver")
                        .long("hs")
                        .value_name("URL")
                        .help("Override homeserver from mxid (for testing)"),
                )
                .arg(
                    clap::Arg::new("skip-verify")
                        .long("skip-verify")
                        .action(clap::ArgAction::SetTrue)
                        .help("Skip the verify phase"),
                ),
        )
        .subcommand(
            clap::Command::new("verify")
                .about("Run the emoji verification (start verification from another session)"),
        )
        .subcommand(
            clap::Command::new("download")
                .about("Download an offer for which you know the event id")
                .arg(
                    clap::Arg::new("url")
                        .index(1)
                        .required(true)
                        .value_name("URL")
                        .help(
                            "Download files offered by a given Matrix event, given as a matrix: \
			     or https://matrix.to url",
                        ),
                )
		.arg(
		    clap::Arg::new("output-dir")
			.long("output")
			.short('O')
			.value_name("DIRECTORY")
			.default_value(".")
			.help("Directory to use for downloading, defaults to ."),
		)
                .arg(
                    clap::Arg::new("redownload")
                        .long("redownload")
                        .action(clap::ArgAction::SetTrue)
                        .help("Download files even if they already exist with the correct checksum"),
                ),
        )
        .subcommand(
            clap::Command::new("offer")
                .about("Offer files to be downloaded in a room")
                .arg(
                    clap::Arg::new("room")
                        .index(1)
                        .required(true)
                        .takes_value(true)
                        .multiple_values(false)
                        .value_name("ROOM")
                        .help("Offer the file in this room"),
                )
                .arg(
                    clap::Arg::new("files")
                        .index(2)
                        .required(true)
                        .takes_value(true)
                        .multiple_values(true)
                        .value_name("FILE")
                        .min_values(1)
                        .help("Files to offer"),
                )
                .arg(
                    clap::Arg::new("max")
                        .long("max")
                        .value_name("MAX")
                        .help("Maximum number of completed uploads before exiting"),
                ),
        )
        .subcommand(
            clap::Command::new("monitor")
                .about("Monitor listed rooms or all rooms for new offers and download them")
                .arg(
                    clap::Arg::new("rooms")
                        .multiple_values(true)
                        .index(1)
                        .required(false)
                        .value_name("ROOM")
                        .min_values(0)
                        .index(1)
                        .help(
                            "Monitor listed rooms for offers and download them when they appear; \
			     if no rooms listed, monitor all.",
                        ),
                )
                .arg(
                    clap::Arg::new("max")
                        .long("max")
                        .value_name("MAX")
                        .help("Maximum number of completed downloads before exiting"),
                )
		.arg(
		    clap::Arg::new("output-dir")
			.long("output")
			.short('O')
			.value_name("DIRECTORY")
			.default_value(".")
			.help("Directory to use for downloading, defaults to ."),
		)
                .arg(
                    clap::Arg::new("redownload")
                        .long("redownload")
                        .action(clap::ArgAction::SetTrue)
                        .help("Download files even if they already exist with the correct checksum"),
                ),
        )
        .arg(
            clap::Arg::new("debug")
                .long("debug")
                .takes_value(true)
		.help(debug_help.as_str()),
        );
    let info_string = app.render_long_version().trim().to_string();
    let args = app.get_matches();

    let _log_guard = init_logging(args.value_of("debug"))?;

    let config_file = setup::get_config_file(args.value_of("config"))?;
    let mut config = config::Config::load(&config_file)?;

    println!("{info_string}");
    match args.subcommand() {
        Some(("setup", sub_args)) => {
            let homeserver = sub_args.value_of("homeserver").map(|x| x.to_string());
            if homeserver.is_some() {
                config.homeserver = homeserver;
            }
            let skip_verify = sub_args.get_flag("skip-verify");
            setup::setup_mode(config, &config_file, !skip_verify).await?
        }
        Some(("monitor", monitor_args)) => {
            let rooms: Vec<String> = monitor_args.values_of_t("rooms").unwrap_or_default();
            let max: Option<usize> = if let Some(value) = monitor_args.value_of("max") {
                Some(value.to_string().parse::<usize>()?)
            } else {
                None
            };
	    let download_options = download::Options {
		output_dir: monitor_args.value_of("output-dir").unwrap().to_string(),
		skip_existing: !monitor_args.get_flag("redownload"),
	    };
            monitor::monitor(
                config,
                download_options,
                if rooms.is_empty() { None } else { Some(rooms) },
		max
            )
            .await?;
        }
        Some(("verify", _sub_args)) => {
            matrix_verify::verify(config).await?;
        }
        Some(("download", download_args)) => {
	    let output_dir = download_args.value_of("output-dir").unwrap();
            let args: Vec<String> = download_args
                .values_of_t("url")
                .expect("clap arguments should ensure this");
            let urls: Vec<&str> = args.iter().map(|x| x.as_str()).collect();
	    let download_options = download::Options {
		output_dir: output_dir.to_string(),
		skip_existing: !download_args.get_flag("redownload"),
	    };
            download::download(config, urls, download_options).await?;
        }
        Some(("offer", offer_args)) => {
            let room_args: Vec<String> = offer_args
                .values_of_t("room")
                .expect("clap arguments should ensure this");
            let room = &room_args[0];
            let files_args: Vec<String> = offer_args
                .values_of_t("files")
                .expect("clap arguments should ensure this");
            let max: Option<usize> = if let Some(value) = offer_args.value_of("max") {
                Some(value.to_string().parse::<usize>()?)
            } else {
                None
            };
            let files: Vec<&str> = files_args.iter().map(|x| x.as_str()).collect();
            offer::offer(config, room, files, max).await?;
        }
        _ => {
            eprintln!("A subcommand is required. --help for help.");
        }
    }

    Ok(())
}
