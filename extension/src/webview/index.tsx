import './styles.css';
import { h, render } from 'preact';
import { App } from './App';

// Main entry point - render the Preact app
render(<App />, document.getElementById('app')!);