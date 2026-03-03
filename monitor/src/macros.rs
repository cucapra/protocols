/// A wrapper around the `log::info!` macro, which includes the name of the
/// function in which the log was called (obtained via `stdext::function_name!`)
macro_rules! info {
    ($($arg:tt)*) => {
        log::info!(
            target: stdext::function_name!().rsplit("::").next().unwrap_or("?"),
            $($arg)*
        )
    }
}

/// Like `info!`, but prefixes the target with `"repeat::"` so logs can be filtered
/// independently of other logs. Use this macro when logging events
/// related to `repeat` loops.
macro_rules! repeat_info {
    ($($arg:tt)*) => {{
        let fn_name = stdext::function_name!().rsplit("::").next().unwrap_or("?");
        let target = std::format!("repeat::{}", fn_name);
        log::info!(target: target.as_str(), $($arg)*)
    }}
}
