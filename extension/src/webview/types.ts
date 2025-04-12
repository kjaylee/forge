// Define the interface for communication between extension and webview
export interface VSCodeMessage {
  command: string;
  text?: string;
}

// Define the VSCode API that's available in the webview
declare global {
  interface Window {
    acquireVsCodeApi: () => {
      postMessage: (message: VSCodeMessage) => void;
      getState: () => any;
      setState: (state: any) => void;
    };
  }
}