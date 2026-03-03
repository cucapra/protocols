/// A wrapper around the `log::info!` macro, which includes the name of the
/// function in which the log was called (obtained via `stdext::function_name!`)
macro_rules! info {
    ($($arg:tt)*) => { log::info!(target: stdext::function_name!(), $($arg)*) }
}
