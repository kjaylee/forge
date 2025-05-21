use forge_domain::Error as DomainError;

use crate::error::Error;
pub fn into_retry(error: anyhow::Error, retry_status_codes: &[u16]) -> anyhow::Error {
    if let Some(code) = get_req_status_code(&error)
        .or(get_event_req_status_code(&error))
        .or(get_api_status_code(&error))
    {
        if retry_status_codes.contains(&code) {
            return DomainError::Retryable(error).into();
        }
    }

    if is_api_transport_error(&error)
        || is_req_transport_error(&error)
        || is_event_transport_error(&error)
    {
        return DomainError::Retryable(error).into();
    }

    error
}

fn get_api_status_code(error: &anyhow::Error) -> Option<u16> {
    error.downcast_ref::<Error>().and_then(|error| match error {
        Error::Response(error) => error
            .get_code_deep()
            .as_ref()
            .and_then(|code| code.as_number()),
        Error::InvalidStatusCode(code) => Some(*code),
        _ => None,
    })
}

fn get_req_status_code(error: &anyhow::Error) -> Option<u16> {
    error
        .downcast_ref::<reqwest::Error>()
        .and_then(|error| error.status())
        .map(|status| status.as_u16())
}

fn get_event_req_status_code(error: &anyhow::Error) -> Option<u16> {
    error
        .downcast_ref::<reqwest_eventsource::Error>()
        .and_then(|error| match error {
            reqwest_eventsource::Error::InvalidStatusCode(_, response) => {
                Some(response.status().as_u16())
            }
            reqwest_eventsource::Error::InvalidContentType(_, response) => {
                Some(response.status().as_u16())
            }
            _ => None,
        })
}

fn is_api_transport_error(error: &anyhow::Error) -> bool {
    error
        .downcast_ref::<Error>()
        .is_some_and(|error| match error {
            Error::Response(error) => error
                .code
                .as_ref()
                .and_then(|code| code.as_str())
                .is_some_and(|code| {
                    ["ERR_STREAM_PREMATURE_CLOSE", "ECONNRESET", "ETIMEDOUT"]
                        .into_iter()
                        .any(|message| message == code)
                }),
            _ => false,
        })
}

fn is_req_transport_error(error: &anyhow::Error) -> bool {
    error
        .downcast_ref::<reqwest::Error>()
        .is_some_and(|e| e.is_timeout() || e.is_connect())
}

fn is_event_transport_error(error: &anyhow::Error) -> bool {
    error
        .downcast_ref::<reqwest_eventsource::Error>()
        .is_some_and(|e| matches!(e, reqwest_eventsource::Error::Transport(_)))
}
