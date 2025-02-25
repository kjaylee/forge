use std::sync::Arc;

use axum::body::Body;
use axum::extract::{FromRequestParts, State};
use axum::http::request::Parts;
use axum::http::Request;
use axum::middleware::Next;
use axum::response::Response;
use clerk_rs::validators::authorizer::{ClerkAuthorizer, ClerkError};
use clerk_rs::validators::axum::AxumClerkRequest;
use serde::Deserialize;

use crate::error::Error;
use crate::service::api_keys::ApiKeyService;

const X_API_KEY_HEADER: &str = "x-api-key";

#[derive(Debug, Clone, Deserialize)]
pub struct AuthUser {
    pub id: String,
}

impl<S> FromRequestParts<S> for AuthUser
where
    S: Send + Sync,
{
    type Rejection = Error;

    async fn from_request_parts(parts: &mut Parts, _state: &S) -> Result<Self, Self::Rejection> {
        parts
            .extensions
            .get::<AuthUser>()
            .cloned()
            .ok_or_else(|| Error::Auth("User not authenticated".to_string()))
    }
}

pub async fn clerk_auth(
    State(authorizer): State<Arc<ClerkAuthorizer>>,
    mut request: Request<Body>,
    next: Next,
) -> Result<Response, Error> {
    let session = authorizer
        .as_ref()
        .authorize(&AxumClerkRequest { headers: request.headers().clone() })
        .await
        .map_err(|e| match e {
            ClerkError::Unauthorized(msg) => Error::Auth(msg),
            ClerkError::InternalServerError(msg) => Error::Service(msg),
        })?;

    request
        .extensions_mut()
        .insert(AuthUser { id: session.sub });

    Ok(next.run(request).await)
}

pub async fn validate_api_key(
    State(service): State<Arc<ApiKeyService>>,
    mut request: Request<Body>,
    next: Next,
) -> Result<Response, Error> {
    let api_key_str = request
        .headers()
        .get(X_API_KEY_HEADER)
        .ok_or_else(|| Error::Auth("Missing API key".to_string()))?
        .to_str()
        .map_err(|_| Error::Auth("Invalid API key".to_string()))?;

    let api_key = service
        .find_by_api_key(api_key_str)
        .await
        .map_err(|_| Error::Auth("Invalid API key".to_string()))?;
    request.extensions_mut().insert(api_key);
    Ok(next.run(request).await)
}
