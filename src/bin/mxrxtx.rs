use mxrxtx::{config, download, matrix_verify, monitor, offer, setup, version::get_version};
use std::io::Write;
use thiserror::Error;

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
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    let args = clap::App::new("mxrxtx")
        .setting(clap::AppSettings::ColoredHelp)
        .setting(clap::AppSettings::ArgRequiredElseHelp)
        .before_help("Licensed under the MIT license")
        .version(get_version().as_str())
        .author("Erkki Seppälä <erkki.seppala@vincit.fi>")
        .about(
            "Transfer files over Matrix, directly from client to client with WebRTC. \n\
	     \n\
	     Licensed under the MIT license; refer to LICENSE.MIT for details.",
        )
        .arg(
            clap::Arg::new("config")
                .long("config")
                .short('c')
                .takes_value(true)
                .value_name("FILE")
                .help(
                    format!(
                        "Config file to load, defaults to {}",
                        setup::get_config_file(None)?
                    )
                    .as_str(),
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
        .subcommand(
            clap::Command::new("setup")
                .about("Run the initial setup")
                .help(
                "Do setup (prompt matrix homeserver address, user account, password, setup e2ee)",
            ),
        )
        .subcommand(
            clap::Command::new("verify")
                .about("Run the emoji verification")
                .help("Run the emoji verification (start verification from another session)"),
        )
        .subcommand(
            clap::Command::new("download")
                .about("Download an offer for which you know the event id")
                .arg(
                    clap::Arg::new("url")
                        .index(1)
                        .required(true)
                        .value_name("URL")
                        .multiple_values(false)
                        .min_values(1)
                        .help(
                            "Download files offered by a given Matrix event, given as a matrix: \
			  or https://matrix.to url",
                        ),
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
                ),
        )
        .arg(clap::Arg::new("trace").long("trace").help("Enable tracing"))
        .get_matches();

    if args.is_present("trace") {
        tracing_subscriber::fmt::init();
    } else {
        env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("mxrxtx=info"))
            .format(|buf, record| {
                writeln!(
                    buf,
                    "{} {:<5} {}",
                    chrono::Local::now().format("%Y-%m-%d %H:%M:%S%.3f"),
                    record.level(),
                    record.args()
                )
            })
            .init();
    }

    let config_file = setup::get_config_file(args.value_of("config"))?;
    let config = config::Config::load(&config_file)?;

    let output_dir = args.value_of("output-dir").unwrap();

    match args.subcommand() {
        Some(("setup", _sub_args)) => setup::setup_mode(args, config, &config_file).await?,
        Some(("monitor", monitor_args)) => {
            let rooms: Vec<String> = monitor_args.values_of_t("rooms").unwrap_or_default();
            monitor::monitor(
                config,
                output_dir,
                if rooms.is_empty() { None } else { Some(rooms) },
            )
            .await?;
        }
        Some(("verify", _sub_args)) => {
            matrix_verify::verify(config).await?;
        }
        Some(("download", download_args)) => {
            let args: Vec<String> = download_args
                .values_of_t("url")
                .expect("clap arguments should ensure this");
            let urls: Vec<&str> = args.iter().map(|x| x.as_str()).collect();
            download::download(config, urls, output_dir).await?;
        }
        Some(("offer", offer_args)) => {
            let room_args: Vec<String> = offer_args
                .values_of_t("room")
                .expect("clap arguments should ensure this");
            let room = &room_args[0];
            let files_args: Vec<String> = offer_args
                .values_of_t("files")
                .expect("clap arguments should ensure this");
            let files: Vec<&str> = files_args[1..files_args.len()]
                .iter()
                .map(|x| x.as_str())
                .collect();
            offer::offer(config, room, files).await?;
        }
        _ => {
            eprintln!("A subcommand is required. --help for help.");
        }
    }

    Ok(())
}
