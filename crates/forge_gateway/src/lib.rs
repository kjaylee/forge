//! Forge Gateway V3 - A modern API gateway for the Forge platform
//!
//! This crate provides a clean 3-tier architecture implementation of the Forge Gateway:
//! - Data layer: Handles persistence and data access
//! - Service layer: Contains business logic and domain operations
//! - Presentation layer: Manages HTTP interfaces and request/response handling

pub mod config;
pub mod data;
pub mod error;
pub mod presentation;
pub mod service;

pub use error::{Error, Result};
pub use data::*;
pub use presentation::*;
pub use service::*;
