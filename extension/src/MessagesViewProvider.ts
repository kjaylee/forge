import * as vscode from 'vscode';
import * as path from 'path';

/**
 * Provider for the messages webview view in the sidebar
 */
export class MessagesViewProvider implements vscode.WebviewViewProvider {
  public static readonly viewType = 'forgeMessages';

  private _view?: vscode.WebviewView;

  constructor(
    private readonly _extensionUri: vscode.Uri,
  ) { }

  resolveWebviewView(
    webviewView: vscode.WebviewView,
    context: vscode.WebviewViewResolveContext,
    _token: vscode.CancellationToken,
  ) {
    this._view = webviewView;

    webviewView.webview.options = {
      // Enable scripts in the webview
      enableScripts: true,
      // Restrict the webview to only loading content from our extension's directory
      localResourceRoots: [this._extensionUri]
    };

    // Set the initial HTML for the webview
    webviewView.webview.html = this._getWebviewContent(webviewView.webview);

    // Handle messages from the webview
    webviewView.webview.onDidReceiveMessage(message => {
      console.log('Received message from webview:', message);
      switch (message.command) {
        case 'addMessage':
          console.log('Processing addMessage command with text:', message.text);
          // Echo the message back to the webview
          webviewView.webview.postMessage({
            command: 'messageAdded',
            text: message.text
          });
          console.log('Sent messageAdded response to webview');
          return;
      }
    });
  }

  /**
   * Get webview script URI
   */
  private _getWebviewScriptUri(webview: vscode.Webview) {
    // Get the local path to the webview bundle
    // This is created by webpack
    const webviewScriptPath = path.join('out', 'webview', 'webview.js');
    
    // And convert it to a URI that can be used within the webview
    const scriptUri = webview.asWebviewUri(
      vscode.Uri.file(path.join(this._extensionUri.fsPath, webviewScriptPath))
    );
    console.log('Script URI:', scriptUri.toString());
    return scriptUri;
  }

  /**
   * Get webview CSS URI
   */
  private _getWebviewStyleUri(webview: vscode.Webview) {
    // Get the local path to the CSS file
    const cssPath = path.join('out', 'webview', 'webview.css');
    
    // And convert it to a URI that can be used within the webview
    const styleUri = webview.asWebviewUri(
      vscode.Uri.file(path.join(this._extensionUri.fsPath, cssPath))
    );
    console.log('Style URI:', styleUri.toString());
    return styleUri;
  }

  /**
   * Get the webview HTML content
   */
  private _getWebviewContent(webview: vscode.Webview) {
    // Get script and style URIs for the webview
    const scriptUri = this._getWebviewScriptUri(webview);
    const styleUri = this._getWebviewStyleUri(webview);
    
    return `<!DOCTYPE html>
      <html lang="en">
      <head>
          <meta charset="UTF-8">
          <meta name="viewport" content="width=device-width, initial-scale=1.0">
          <meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src ${webview.cspSource}; script-src ${webview.cspSource};">
          <title>Forge Messages</title>
          <link rel="stylesheet" href="${styleUri}">
      </head>
      <body>
          <div id="app"></div>
          <script>
              // Add error handling wrapper
              window.addEventListener('error', (event) => {
                  console.error('Error in webview:', event.error);
              });
          </script>
          <script src="${scriptUri}"></script>
      </body>
      </html>`;
  }
}