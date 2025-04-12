// The module 'vscode' contains the VS Code extensibility API
import * as vscode from 'vscode';
import { MessagesViewProvider } from './MessagesViewProvider';

/**
 * This method is called when your extension is activated
 */
export function activate(context: vscode.ExtensionContext) {
  console.log('Extension "forge" is now active!');

  // Register the message view provider for the sidebar
  const messageViewProvider = new MessagesViewProvider(context.extensionUri);
  const messageViewDisposable = vscode.window.registerWebviewViewProvider(
    MessagesViewProvider.viewType, 
    messageViewProvider
  );

  context.subscriptions.push(messageViewDisposable);
}

/**
 * This method is called when your extension is deactivated
 */
export function deactivate() {}