/**
 * DEPRECATED: This file is maintained for backward compatibility.
 * Please import directly from '@/utils/filePathUtils' instead.
 */
import { File as FileIcon } from 'lucide-react';

// Re-export all functionality from the new location
export * from '@/utils/filePathUtils';

/**
 * Extracts line number from a file path if present
 * 
 * @param path The path that might contain a line number
 * @returns An object with the cleaned path and optional line number
 */
export interface PathWithLineNumber {
  path: string;
  lineNumber: number | null;
}

export const extractLineNumber = (path: string): PathWithLineNumber => {
  // Check for common patterns like file.js:42 or file.js#L42 or file.js(42)
  const linePatterns = [
    /^(.+):(\d+)$/, // file.js:42
    /^(.+)#L(\d+)$/, // file.js#L42
    /^(.+)\((\d+)\)$/, // file.js(42)
    /^(.+) line (\d+)$/, // file.js line 42
  ];

  for (const pattern of linePatterns) {
    const match = path.match(pattern);
    if (match && match[1] && match[2]) {
      return {
        path: match[1],
        lineNumber: parseInt(match[2], 10)
      };
    }
  }

  return { path, lineNumber: null };
};

/**
 * Checks if a string appears to be a valid file path
 * 
 * @param text The text to check
 * @returns boolean indicating if text is likely a file path
 */
export const isFilePath = (text: string): boolean => {
  // First, extract any line numbers
  const { path } = extractLineNumber(text);
  
  // Patterns to identify likely file paths
  // 1. Absolute paths (Unix-like)
  const unixAbsolutePathPattern = /^\/([^/\0]+(\/)?)+$/;
  
  // 2. Absolute paths (Windows-like)
  const windowsAbsolutePathPattern = /^[A-Za-z]:((\\|\/)[^\\/:*?"<>|\0]+)+$/;
  
  // 3. Relative paths with file extension (avoid mismatching URLs)
  const relativeFilePathPattern = /^(\.{1,2}\/)?([^\/\0]+\/)*([\w-]+(\.[\w-]+)+)$/;
  
  // 4. Simple filename with extension (avoid matching single words)
  const fileNameWithExtensionPattern = /^[\w-][\w\s-]*\.\w{1,10}$/;
  
  // 5. Common project paths
  const projectPathPattern = /^(src|lib|app|test|tests|dist|build)\/[\w\/\.-]+$/;

  return (
    unixAbsolutePathPattern.test(path) ||
    windowsAbsolutePathPattern.test(path) ||
    relativeFilePathPattern.test(path) ||
    fileNameWithExtensionPattern.test(path) ||
    projectPathPattern.test(path)
  );
};

/**
 * Finds file paths within a text string
 * 
 * @param text The text to search for file paths
 * @returns An array of identified file paths
 */
export const findFilePaths = (text: string): string[] => {
  // First, try to find paths that are explicitly marked with backticks or quotes
  const markedPathsPattern = /(`|"|')((?:\/|\.\/|\.\.\/|[A-Za-z]:\\)(?:[^`"'\0])+)(?:`|"|')/g;
  const matches: string[] = [];
  
  let match: RegExpExecArray | null;
  while ((match = markedPathsPattern.exec(text)) !== null) {
    if (isFilePath(match[2])) {
      matches.push(match[2]);
    }
  }
  
  // Then look for unmarked paths
  const words = text.split(/\s+/);
  for (const word of words) {
    // Avoid re-checking paths we've already found
    if (!matches.includes(word) && isFilePath(word)) {
      matches.push(word);
    }
  }
  
  return matches;
};

/**
 * Wraps file paths in text with clickable elements
 * 
 * @param text The text containing file paths
 * @param handleClick Function to call when a file path is clicked
 * @returns React elements with clickable file paths
 */
export const makeFilePathsClickable = (text: string, handleClick: (path: string) => void): JSX.Element => {
  if (!text) return <></>;
  
  const paths = findFilePaths(text);
  if (paths.length === 0) return <p>{text}</p>;
  
  // Sort by length (longest first) to prevent matching substrings
  paths.sort((a, b) => b.length - a.length);
  
  // Split the text by file paths and create React elements
  let result: JSX.Element[] = [];
  let currentText = text;
  
  paths.forEach((path, index) => {
    // Extract any line number before processing
    const { path: cleanPath, lineNumber } = extractLineNumber(path);
    
    // Split current text by this path
    const parts = currentText.split(path);
    
    // Add all parts except the last one, with clickable paths in between
    for (let i = 0; i < parts.length - 1; i++) {
      // Add the text before the path
      if (parts[i]) {
        result.push(<span key={`text-${index}-${i}`}>{parts[i]}</span>);
      }
      
      // Add the clickable path with enhanced styling
      result.push(
        <span 
          key={`path-${index}-${i}`}
          className="inline-flex items-center text-blue-600 hover:text-blue-800 cursor-pointer hover:bg-blue-50 px-1 py-0.5 rounded-sm gap-1 group whitespace-nowrap"
          onClick={() => {
            // Pass both path and line number to the handler
            if (lineNumber) {
              handleClick(`${cleanPath}:${lineNumber}`);
            } else {
              handleClick(cleanPath);
            }
          }}
          title={`Open ${path}`}
        >
          <FileIcon className="h-3 w-3 opacity-70 group-hover:opacity-100" />
          <span className="group-hover:underline">{path}</span>
          {lineNumber && (
            <span className="bg-blue-100 text-blue-800 text-xs px-1 rounded-sm">{lineNumber}</span>
          )}
        </span>
      );
    }
    
    // Update currentText to be the last part
    currentText = parts[parts.length - 1];
  });
  
  // Add any remaining text
  if (currentText) {
    result.push(<span key="remaining-text">{currentText}</span>);
  }
  
  return <p className="whitespace-pre-wrap">{result}</p>;
};