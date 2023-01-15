use mxrxtx::{config, download, matrix_verify, monitor, offer, setup, version::get_version};

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
                        setup::get_config_file(None)?
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
            clap::Arg::new("setup")
                .long("setup")
                .help("Do setup (prompt matrix homeserver address, user account, password, TODO: setup e2ee)"),
        )
        .arg(
            clap::Arg::new("verify")
                .long("verify")
                .help("Run emoji verification (start verification from another session)"),
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
        .arg(clap::Arg::new("monitor")
                .short('m')
                .long("monitor")
                .multiple_values(true)
                .min_values(0)
                .help("Monitor listed rooms for offers and download them when they appear; if no rooms listed, monitor all."),
        )
        .arg(clap::Arg::new("trace")
             .long("trace")
             .help("Enable tracing"))
	.group(clap::ArgGroup::new("mode")
               .args(&["offer", "download", "setup", "verify", "monitor"])
               .required(true))
        .get_matches();

    if args.is_present("trace") {
        tracing_subscriber::fmt::init();
    } else {
        env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("mxrxtx=info"))
            .init();
    }

    let config_file = setup::get_config_file(args.value_of("config"))?;
    let config = config::Config::load(&config_file)?;

    let output_dir = args.value_of("output-dir").unwrap();

    if args.is_present("setup") {
        setup::setup_mode(args, config, &config_file).await?
    } else if args.is_present("monitor") {
        let rooms: Vec<String> = args
            .values_of_t("monitor")
            .expect("clap arguments should ensure this");
        monitor::monitor(
            config,
            output_dir,
            if rooms.is_empty() { None } else { Some(rooms) },
        )
        .await?;
    } else if args.is_present("verify") {
        matrix_verify::verify(config).await?;
    } else if args.is_present("download") {
        let args: Vec<String> = args
            .values_of_t("download")
            .expect("clap arguments should ensure this");
        let urls: Vec<&str> = args.iter().map(|x| x.as_str()).collect();
        download::download(config, urls, output_dir).await?;
    } else if args.is_present("offer") {
        let args: Vec<String> = args
            .values_of_t("offer")
            .expect("clap arguments should ensure this");
        let room = &args[0];
        let files: Vec<&str> = args[1..args.len()].iter().map(|x| x.as_str()).collect();
        offer::offer(config, room, files).await?;
    } else {
        panic!("Clap group should ensure at least one of these is set..");
    }

    Ok(())
}
