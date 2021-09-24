pub fn get_version() -> String {
    String::from(option_env!("GIT_DESCRIBE").unwrap_or_else(|| env!("VERGEN_SEMVER")))
}
