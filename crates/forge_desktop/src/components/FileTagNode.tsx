import { Node, mergeAttributes } from '@tiptap/core';
import { ReactNodeViewRenderer } from '@tiptap/react';
import { X } from 'lucide-react';
import { Tooltip, TooltipContent, TooltipProvider, TooltipTrigger } from '@/components/ui/tooltip';

export interface FileTagAttrs {
  filePath: string;
  id: string;
}

// Helper function to get basename from a path
const getBasename = (filepath: string): string => {
  const normalizedPath = filepath.replace(/\\/g, '/');
  const parts = normalizedPath.split('/');
  return parts[parts.length - 1] || filepath;
};

// React component for rendering the FileTag
const FileTagComponent = (props: {
  node: { attrs: FileTagAttrs };
  deleteNode: () => void;
}) => {
  const { filePath } = props.node.attrs;
  const fileName = getBasename(filePath);

  return (
    <TooltipProvider>
      <Tooltip delayDuration={300}>
        <TooltipTrigger asChild>
          <span // Using span instead of div to fit better inline
            contentEditable={false} // Important - prevents the node from being edited
            className="inline-flex items-center bg-blue-50 border border-blue-100 rounded-md py-0.5 px-1.5 mr-1 my-0 mx-0.5 text-xs whitespace-nowrap hover:bg-blue-100 transition-colors"
            data-file-tag
          >
            <span className="truncate max-w-[120px] text-blue-700 font-medium">
              {fileName}
            </span>
            <button
              onClick={(e) => {
                e.preventDefault();
                props.deleteNode();
              }}
              className="ml-1 text-muted-foreground hover:text-destructive transition-colors"
              aria-label="Remove file tag"
            >
              <X className="h-3 w-3" />
            </button>
          </span>
        </TooltipTrigger>
        <TooltipContent side="top">
          <p className="max-w-[300px] break-all text-xs">{filePath}</p>
        </TooltipContent>
      </Tooltip>
    </TooltipProvider>
  );
};

// TipTap Node definition
const FileTagNode = Node.create<{ onRemove?: (filePath: string) => void }>({
  name: 'fileTag',
  
  group: 'inline',
  
  inline: true,
  
  selectable: false,
  
  atom: true, // Treat the node as a single unit
  
  addAttributes() {
    return {
      filePath: {
        default: null
      },
      id: {
        default: null
      }
    };
  },
  
  parseHTML() {
    return [
      {
        tag: 'span[data-file-tag]'
      }
    ];
  },
  
  renderHTML({ HTMLAttributes }) {
    return ['span', mergeAttributes(HTMLAttributes, { 'data-file-tag': '' }), 0];
  },
  
  addNodeView() {
    return ReactNodeViewRenderer((props: any) => {
      return (
        <FileTagComponent
          node={props.node}
          deleteNode={() => {
            props.deleteNode();
            // If onRemove callback is provided, call it with the file path
            if (this.options.onRemove) {
              this.options.onRemove(props.node.attrs.filePath);
            }
          }}
        />
      );
    });
  }
});

export default FileTagNode;