use indicatif::{MultiProgress, ProgressBar, ProgressFinish, ProgressState, ProgressStyle};
use std::time::Duration;

pub fn make_transfer_progress(len: u64, multi: Option<&MultiProgress>) -> ProgressBar {
    let progress = ProgressBar::new(len).with_finish(ProgressFinish::AndClear);
    let progress = if let Some(multi) = multi {
        multi.add(progress)
    } else {
        progress
    };
    progress.
	set_style(ProgressStyle::with_template("{spinner:.green} {prefix}[{elapsed_precise}] [{wide_bar:.cyan/blue}] {bytes}/{total_bytes} {speed} {eta}")
		  .unwrap()
		  .with_key("speed",
			    |state: &ProgressState, w: &mut dyn std::fmt::Write| {
				write!(w, "{:.1}MiB/s",
				       state.per_sec() / 1000000.0).unwrap()
			    }
		  )
		  .with_key("eta",
			    |state: &ProgressState, w: &mut dyn std::fmt::Write| {
				write!(w, "ETA {:.0}s",
				       state.eta().as_secs_f64()).unwrap()
			    }));
    progress
}

pub fn make_spinner(multi: Option<&MultiProgress>) -> ProgressBar {
    let spinner = ProgressBar::new_spinner();
    let spinner = if let Some(multi) = multi {
        multi.add(spinner)
    } else {
        spinner
    };
    spinner.set_style(ProgressStyle::with_template("{spinner:.green} {msg}").unwrap());
    spinner.enable_steady_tick(Duration::from_millis(200));
    spinner
}
