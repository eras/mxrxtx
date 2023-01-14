// Sprinkle some paranoia when printing network- or user-provided data
// to avoid messing up terminals remotely.
pub fn escape(data: &str) -> String {
    data.to_string()
        .chars()
        .map(|char| char.escape_default().to_string())
        .collect()
}

// Remove the possibility of directory traversal by hostile e.g. homeserver responses or offers
pub fn escape_paths(data: &str) -> String {
    data.to_string()
        .chars()
        .map(|char| match char {
            '\\' | '/' => "_".to_string(),
            other => other.to_string(),
        })
        .collect()
}
