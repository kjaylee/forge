use std::net::{IpAddr, Ipv4Addr, SocketAddr};

/// Configuration for the Forge HTTP server
#[derive(Clone, Debug)]
pub struct ServerConfig {
    /// The address to bind to
    pub host: IpAddr,
    /// The port to bind to
    pub port: u16,
    /// Whether to enable CORS
    pub enable_cors: bool,
    /// Whether to use restricted mode for the forge API
    pub restricted: bool,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            host: IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)),
            port: 3000,
            enable_cors: true,
            restricted: true,
        }
    }
}

impl ServerConfig {
    /// Create a new builder instance with default values
    pub fn builder() -> ServerConfigBuilder {
        ServerConfigBuilder::default()
    }
}

/// Builder for ServerConfig
#[derive(Default)]
pub struct ServerConfigBuilder {
    config: ServerConfig,
}

impl ServerConfigBuilder {
    /// Set the host to bind to
    pub fn host(mut self, host: IpAddr) -> Self {
        self.config.host = host;
        self
    }

    /// Set the port to bind to
    pub fn port(mut self, port: u16) -> Self {
        self.config.port = port;
        self
    }

    /// Enable or disable CORS
    pub fn enable_cors(mut self, enable: bool) -> Self {
        self.config.enable_cors = enable;
        self
    }

    /// Enable or disable restricted mode
    pub fn restricted(mut self, restricted: bool) -> Self {
        self.config.restricted = restricted;
        self
    }

    /// Build the server config
    pub fn build(self) -> ServerConfig {
        self.config
    }
}

/// Helper to get socket address from config
pub(crate) fn get_socket_addr(config: &ServerConfig) -> SocketAddr {
    SocketAddr::new(config.host, config.port)
}
