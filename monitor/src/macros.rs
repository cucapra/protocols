/// Takes the output of `stdext::debug_name!` (in the `debug_name` argument)
/// and extracts the file name, line number and function name where
/// the log was called, returning a formatted string of
/// the form `file_name:line (function_name)`.
pub fn compact_debug_prefix(debug_name: &str) -> String {
    // `stdext::debug_name!` returns strings in the form
    // "<function name> at <file location>`, so we have to split on "at"
    let mut debug_parts = debug_name.split(" at ");
    let loc = debug_parts.next().unwrap_or("?:0");
    let fn_path = debug_parts.next().unwrap_or("?");
    let mut loc_parts = loc.rsplitn(2, ':');
    let line = loc_parts.next().unwrap_or("0");
    // `stdext::debug_name!` gives us the full filepath
    // we just need the stem of the filepath (the file name)
    let file_path = loc_parts.next().unwrap_or(loc);
    let file = std::path::Path::new(file_path)
        .file_name()
        .and_then(|f| f.to_str())
        .unwrap_or(file_path);
    let fn_name = fn_path.rsplit("::").next().unwrap_or(fn_path);
    format!("{}:{} ({})", file, line, fn_name)
}

/// A wrapper around the `log::info!` macro, which includes the function name,
/// file name and line number in which the log was called
/// (obtained via `stdext::debug_name!`)
macro_rules! info {
    ($($arg:tt)*) => {{
        let location = crate::macros::compact_debug_prefix(&stdext::debug_name!());
        log::info!(
            target: "info",
            "{}: {}",
            location,
            format_args!($($arg)*)
        )
    }}
}

/// Like `info!`, but prefixes the target with `"repeat::"` so logs can be filtered
/// independently of other logs. Use this macro when logging events
/// related to `repeat` loops.
macro_rules! repeat_info {
    ($($arg:tt)*) => {{
        let location = crate::macros::compact_debug_prefix(&stdext::debug_name!());
        log::info!(
            target: "repeat",
            "{}: {}",
            location,
            format_args!($($arg)*)
        )
    }}
}
