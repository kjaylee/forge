import React from 'react';
import { X } from 'lucide-react';
import { Tooltip, TooltipContent, TooltipProvider, TooltipTrigger } from '@/components/ui/tooltip';

interface FileTagProps {
  filePath: string;
  onRemove: () => void;
}

// Helper function to get basename from a path (replaces path.basename functionality)
const getBasename = (filepath: string): string => {
  // Handle both Windows and Unix-style paths
  const normalizedPath = filepath.replace(/\\/g, '/');
  const parts = normalizedPath.split('/');
  return parts[parts.length - 1] || filepath;
};

const FileTag: React.FC<FileTagProps> = ({ filePath, onRemove, inline = false }) => {
  // Extract just the filename from the path using our custom function
  const fileName = getBasename(filePath);

  return (
    <TooltipProvider>
      <Tooltip delayDuration={300}>
        <TooltipTrigger asChild>
          <div className={`inline-flex items-center bg-blue-50 border border-blue-100 rounded-md py-0.5 px-1.5 mr-1 ${inline ? 'my-0 mx-0.5' : 'mb-1'} text-xs group whitespace-nowrap hover:bg-blue-100 transition-colors`}>
            <span className="truncate max-w-[120px] text-blue-700 font-medium">{fileName}</span>
            <button 
              onClick={(e) => {
                e.preventDefault();
                onRemove();
              }}
              className="ml-1 text-muted-foreground hover:text-destructive transition-colors"
              aria-label="Remove file tag"
            >
              <X className="h-3 w-3" />
            </button>
          </div>
        </TooltipTrigger>
        <TooltipContent side="top">
          <p className="max-w-[300px] break-all text-xs">{filePath}</p>
        </TooltipContent>
      </Tooltip>
    </TooltipProvider>
  );
};

export default FileTag;