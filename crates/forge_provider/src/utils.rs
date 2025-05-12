use std::error::Error;

use reqwest::StatusCode;

/// Helper function to format HTTP request/response context for logging and
/// error reporting
pub(crate) fn format_http_context<U: AsRef<str>>(
    status: Option<StatusCode>,
    method: &str,
    url: U,
) -> String {
    if let Some(status) = status {
        format!("{} {} {}", status.as_u16(), method, url.as_ref())
    } else {
        format!("{} {}", method, url.as_ref())
    }
}

/// Utility function to detect if an error is a TLS handshake EOF error
/// Returns true if the error contains std::io::ErrorKind::UnexpectedEof
/// ref: https://docs.rs/rustls/latest/rustls/manual/_03_howto/index.html#unexpected-eof
pub(crate) fn is_tls_handshake_eof(err: &(dyn Error + 'static)) -> bool {
    // Check if the error itself is an UnexpectedEof
    if let Some(io_err) = err.downcast_ref::<std::io::Error>() {
        if io_err.kind() == std::io::ErrorKind::UnexpectedEof {
            return true;
        }
    }

    // Then recursively check the error chain
    let mut source = err.source();
    while let Some(current_err) = source {
        // Check for UnexpectedEof in the current error
        if let Some(io_err) = current_err.downcast_ref::<std::io::Error>() {
            if io_err.kind() == std::io::ErrorKind::UnexpectedEof {
                return true;
            }

            // Check for nested UnexpectedEof in custom error sources
            if let Some(custom) = io_err.get_ref() {
                if let Some(nested_err) = custom.downcast_ref::<std::io::Error>() {
                    if nested_err.kind() == std::io::ErrorKind::UnexpectedEof {
                        return true;
                    }
                }
            }
        }

        // Move to the next error in the chain
        source = current_err.source();
    }

    false
}
