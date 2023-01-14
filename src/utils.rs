// Sprinkle some paranoia when printing network- or user-provided data
// to avoid messing up terminals remotely.
pub fn escape(data: &str) -> String {
    data.to_string()
        .chars()
        .map(|char| char.escape_default().to_string())
        .collect()
}
