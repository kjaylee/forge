import { useFileViewerStore } from '@/stores/FileViewerStore';

// Define type for file path detection options
interface FilePathDetectionOptions {
  detectRelative?: boolean;
  enableLineNumbers?: boolean;
  baseDir?: string; // Used for converting relative paths to absolute paths
}

// Default options
const defaultOptions: FilePathDetectionOptions = {
  detectRelative: true,
  enableLineNumbers: true,
  baseDir: undefined
};

/**
 * Utility to extract file paths from text.
 * Can detect both absolute and relative paths.
 */
export function detectFilePaths(text: string, options: FilePathDetectionOptions = {}): RegExpMatchArray[] {
  const opts = { ...defaultOptions, ...options };
  
  // Patterns to detect file paths in text
  const patterns = [
    // Absolute paths: /path/to/file.ext or /path/to/file.ext:123 (with line numbers)
    // For macOS and Linux
    /\/((?:[\w.-]+\/)*[\w.-]+\.\w+)(?::(\d+))?/g,
    
    // Windows absolute paths: C:\path\to\file.ext or C:\path\to\file.ext:123 (with line numbers)
    /([A-Z]:\\(?:[\w.-]+\\)*[\w.-]+\.\w+)(?::(\d+))?/gi
  ];
  
  // If detecting relative paths is enabled
  if (opts.detectRelative) {
    // Relative paths like './src/file.js' or '../components/Button.tsx:42'
    patterns.push(/(\.{1,2}\/(?:[\w.-]+\/)*[\w.-]+\.\w+)(?::(\d+))?/g);
    
    // Simple file references like 'file.js' or 'components/Button.tsx:42'
    patterns.push(/\b((?:[\w.-]+\/)*[\w.-]+\.\w{1,10})(?::(\d+))?(?=\s|$|\)|\]|\}|,|\.|\?)/g);
  }
  
  let matches: RegExpMatchArray[] = [];
  
  // Execute each pattern to find all matches
  for (const pattern of patterns) {
    let match;
    while ((match = pattern.exec(text)) !== null) {
      matches.push(match);
    }
  }
  
  return matches;
}

/**
 * React component that renders text with clickable file paths
 */
interface FilePathTextProps {
  text: string;
  options?: FilePathDetectionOptions;
  className?: string;
  // Custom renderer for matched paths (optional)
  renderPath?: (path: string, line: string | undefined, openFile: () => void) => JSX.Element;
}

export const FilePathText: React.FC<FilePathTextProps> = ({ 
  text,
  options = {},
  className = '',
  renderPath
}) => {
  const { openFile } = useFileViewerStore();
  
  if (!text) return null;
  
  const paths = detectFilePaths(text, options);
  
  // If no file paths detected, just return the original text
  if (paths.length === 0) {
    return <span className={className}>{text}</span>;
  }
  
  // Track positions for slicing the text
  let lastIndex = 0;
  const elements: JSX.Element[] = [];
  
  // Process each match
  paths.forEach((match, idx) => {
    const [fullMatch, filePath, lineNumber] = match;
    const startIndex = match.index || 0;
    
    // Add text before the match
    if (startIndex > lastIndex) {
      elements.push(
        <span key={`text-${idx}`}>
          {text.substring(lastIndex, startIndex)}
        </span>
      );
    }
    
    // Determine the path to open
    let pathToOpen = filePath;
    
    // Convert relative path to absolute if baseDir is provided
    if (options.baseDir && (filePath.startsWith('./') || filePath.startsWith('../') || !filePath.startsWith('/'))) {
      // Simple path joining for demonstration - might need more robust handling
      pathToOpen = `${options.baseDir}/${filePath}`;
    }
    
    // Generate full path including line number if available
    const fullPath = lineNumber ? `${pathToOpen}:${lineNumber}` : pathToOpen;
    
    // Handler for clicking on the path
    const handleOpen = () => {
      openFile(fullPath);
    };
    
    // Add the clickable path element
    if (renderPath) {
      // Use custom renderer if provided
      elements.push(renderPath(filePath, lineNumber, handleOpen));
    } else {
      // Default rendering
      elements.push(
        <span 
          key={`path-${idx}`}
          onClick={handleOpen}
          className="text-blue-600 dark:text-blue-400 hover:underline cursor-pointer font-mono"
          title={`Open ${fullPath}`}
        >
          {fullMatch}
        </span>
      );
    }
    
    lastIndex = startIndex + fullMatch.length;
  });
  
  // Add any remaining text
  if (lastIndex < text.length) {
    elements.push(
      <span key="text-end">
        {text.substring(lastIndex)}
      </span>
    );
  }
  
  return <span className={className}>{elements}</span>;
};

/**
 * Component for displaying a clickable file path with an icon
 */
export const FilePathLink: React.FC<{
  filePath: string;
  lineNumber?: number | string;
  className?: string;
}> = ({ filePath, lineNumber, className = '' }) => {
  const { openFile } = useFileViewerStore();
  
  const handleClick = () => {
    const path = lineNumber ? `${filePath}:${lineNumber}` : filePath;
    openFile(path);
  };
  
  return (
    <span 
      onClick={handleClick}
      className={`inline-flex items-center cursor-pointer hover:underline text-blue-600 dark:text-blue-400 ${className}`}
      title={`Open ${filePath}${lineNumber ? ` at line ${lineNumber}` : ''}`}
    >
      <svg 
        className="mr-1 h-3.5 w-3.5"
        xmlns="http://www.w3.org/2000/svg" 
        viewBox="0 0 24 24" 
        fill="none" 
        stroke="currentColor" 
        strokeWidth="2" 
        strokeLinecap="round" 
        strokeLinejoin="round"
      >
        <path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"></path>
        <polyline points="14 2 14 8 20 8"></polyline>
        <line x1="16" y1="13" x2="8" y2="13"></line>
        <line x1="16" y1="17" x2="8" y2="17"></line>
        <polyline points="10 9 9 9 8 9"></polyline>
      </svg>
      {filePath}
      {lineNumber && <span className="ml-1 text-xs opacity-75">(line {lineNumber})</span>}
    </span>
  );
};