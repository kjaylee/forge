import { h } from 'preact';
import { useState, useEffect, useRef } from 'preact/hooks';

// Type for messages from the extension
interface Message {
  command: string;
  text?: string;
}

// Message type
interface MessageItem {
  id: number;
  text: string;
}

export function App() {
  const [messages, setMessages] = useState<MessageItem[]>([]);
  const [inputText, setInputText] = useState('');
  const [vscode, setVscode] = useState<any | undefined>(undefined);
  const messagesEndRef = useRef<HTMLDivElement>(null);

  // Initialize vscode API access
  useEffect(() => {
    // Access the VS Code API
    // Note: acquireVsCodeApi can only be called once, so we need to store it
    const vscodeApi = acquireVsCodeApi();
    setVscode(vscodeApi);

    // Handle messages from the extension
    window.addEventListener('message', event => {
      const message = event.data as Message;
      console.log('Received message in webview:', message);
      
      if (message.command === 'messageAdded' && message.text) {
        addMessage(message.text);
      }
    });
  }, []);

  // Scroll to bottom when messages change
  useEffect(() => {
    scrollToBottom();
  }, [messages]);

  const scrollToBottom = () => {
    messagesEndRef.current?.scrollIntoView({ behavior: 'smooth' });
  };

  const addMessage = (text: string) => {
    setMessages(prevMessages => [
      ...prevMessages,
      { id: Date.now(), text }
    ]);
  };

  const handleSendMessage = () => {
    if (!inputText.trim() || !vscode) return;

    console.log('Sending message to extension:', inputText);
    
    // Send message to VS Code extension
    vscode.postMessage({
      command: 'addMessage',
      text: inputText
    });
    
    // Clear input field
    setInputText('');
  };

  const handleKeyPress = (e: KeyboardEvent) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault();
      handleSendMessage();
    }
  };

  return (
    <div className="message-container">
      <div className="messages-display">
        {messages.map((message) => (
          <div key={message.id} className="message-item">
            {message.text}
          </div>
        ))}
        <div ref={messagesEndRef} />
      </div>
      
      <div className="input-container">
        <div className="input-flex">
          <textarea
            value={inputText}
            onInput={(e) => setInputText((e.target as HTMLTextAreaElement).value)}
            onKeyPress={handleKeyPress}
            className="message-input"
            placeholder="Type a message..."
          />
          <button 
            onClick={handleSendMessage}
            className="send-button"
          >
            Send
          </button>
        </div>
      </div>
    </div>
  );
}

// Declare the VS Code API type
declare function acquireVsCodeApi(): any;