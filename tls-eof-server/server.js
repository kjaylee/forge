const tls = require('tls');
const fs = require('fs');
const path = require('path');

function logWithTimestamp(message) {
    const timestamp = new Date().toISOString();
    console.log(`[${timestamp}] ${message}`);
}

const options = {
    key: fs.readFileSync('key.pem'),
    cert: fs.readFileSync('cert.pem'),
};

// Create TLS server
const server = tls.createServer(options, (socket) => {
    const clientId = `${socket.remoteAddress}:${socket.remotePort}`;
    logWithTimestamp(`New client connection from ${clientId}`);

    // Log TLS version and cipher once handshake is complete
    socket.on('secure', () => {
        logWithTimestamp(`TLS handshake completed for ${clientId}:`);
        logWithTimestamp(`  - Protocol: ${socket.getProtocol()}`);
        logWithTimestamp(`  - Cipher: ${socket.getCipher().name}`);
    });

    // Simulate different types of connection drops:
    const dropTypes = ['immediate', 'partial', 'delayed'];
    const dropType = dropTypes[Math.floor(Math.random() * dropTypes.length)];
    logWithTimestamp(`Selected drop type for ${clientId}: ${dropType}`);

    switch (dropType) {
        case 'immediate':
            // Immediately destroy the socket
            logWithTimestamp(`[${dropType}] Dropping connection immediately for ${clientId}`);
            socket.destroy();
            break;

        case 'partial':
            // Allow partial handshake then drop
            logWithTimestamp(`[${dropType}] Waiting for first data packet from ${clientId}`);
            socket.once('data', (data) => {
                logWithTimestamp(`[${dropType}] Received ${data.length} bytes from ${clientId}, dropping connection`);
                socket.destroy();
            });
            break;

        case 'delayed':
            // Wait a bit then drop the connection
            logWithTimestamp(`[${dropType}] Waiting 100ms before dropping connection for ${clientId}`);
            setTimeout(() => {
                logWithTimestamp(`[${dropType}] Timeout reached, dropping connection for ${clientId}`);
                socket.destroy();
            }, 100);
            break;
    }

    // Log socket events
    socket.on('error', (err) => {
        logWithTimestamp(`Socket error for ${clientId}: ${err.message}`);
    });

    socket.on('end', () => {
        logWithTimestamp(`Client ${clientId} ended connection`);
    });

    socket.on('close', (hadError) => {
        logWithTimestamp(`Connection closed for ${clientId} ${hadError ? 'due to error' : 'cleanly'}`);
    });
});

// Log server events
server.on('error', (err) => {
    logWithTimestamp(`Server error: ${err.message}`);
});

server.on('tlsClientError', (err, tlsSocket) => {
    const clientId = `${tlsSocket.remoteAddress}:${tlsSocket.remotePort}`;
    logWithTimestamp(`TLS client error for ${clientId}: ${err.message}`);
});

const PORT = 9443;
server.listen(PORT, () => {
    logWithTimestamp(`TLS EOF server listening on port ${PORT}`);
    logWithTimestamp('To test with curl:');
    logWithTimestamp(`curl --insecure https://localhost:${PORT}`);
});
