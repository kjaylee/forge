import React, { useEffect } from 'react';
import { useEditor, EditorContent, Extension } from '@tiptap/react';
import StarterKit from '@tiptap/starter-kit';
import { Node } from '@tiptap/pm/model';
import { Plugin, PluginKey } from '@tiptap/pm/state';
import { FileTagAttrs } from './FileTagNode';
import FileTagNode from './FileTagNode';
import { cn } from '@/lib/utils';

interface TipTapEditorProps {
  content: string;
  onChange: (text: string) => void;
  onSubmit: () => void;
  taggedFiles: string[];
  onRemoveFile: (index: number) => void;
  onFileDrop: (path: string) => void;
  disabled?: boolean;
  isDragging: boolean;
  placeholder?: string;
  className?: string;
}

// Create SubmitExtension to handle Enter for submission
const SubmitExtension = Extension.create({
  name: 'submitExtension',
  
  addProseMirrorPlugins() {
    const onSubmit = this.options.onSubmit;
    
    return [
      new Plugin({
        key: new PluginKey('submitExtension'),
        props: {
          handleKeyDown(view, event) {
            if (event.key === 'Enter' && !event.shiftKey) {
              event.preventDefault();
              if (onSubmit) onSubmit();
              return true;
            }
            
            // Handle Backspace key to remove the last tag when at the beginning of an empty document
            if (event.key === 'Backspace' && view.state.doc.textContent === '' && view.state.doc.childCount === 1) {
              const { removeLastTag } = this.options;
              if (removeLastTag) {
                removeLastTag();
                return true;
              }
            }
            
            return false;
          }
        }
      })
    ];
  },
  
  addOptions() {
    return {
      onSubmit: () => {},
      removeLastTag: () => {}
    };
  }
});

// Create extension to handle file dropping
const FileDropExtension = Extension.create({
  name: 'fileDrop',
  
  addProseMirrorPlugins() {
    const onFileDrop = this.options.onFileDrop;
    
    return [
      new Plugin({
        key: new PluginKey('fileDrop'),
        props: {
          handleDOMEvents: {
            dragover(view, event) {
              // Make sure we can handle this drop
              if (event.dataTransfer && event.dataTransfer.types.includes('text/plain')) {
                event.preventDefault();
                return true;
              }
              return false;
            },
            drop(view, event) {
              // Stop propagation to allow for our own handling
              event.stopPropagation();
              
              if (event.dataTransfer && event.dataTransfer.types.includes('text/plain')) {
                const filePath = event.dataTransfer.getData('text/plain');
                if (filePath) {
                  onFileDrop(filePath);
                  event.preventDefault();
                  return true;
                }
              }
              return false;
            }
          }
        }
      })
    ];
  },
  
  addOptions() {
    return {
      onFileDrop: () => {}
    };
  }
});

const TipTapEditor: React.FC<TipTapEditorProps> = ({
  content,
  onChange,
  onSubmit,
  taggedFiles,
  onRemoveFile,
  onFileDrop,
  disabled = false,
  isDragging,
  placeholder = 'Type a message or drop files here...',
  className
}) => {
  const editor = useEditor({
    extensions: [
      StarterKit.configure({
        heading: false,
        bulletList: false,
        orderedList: false,
        blockquote: false,
        codeBlock: false,
      }),
      FileTagNode,
      SubmitExtension.configure({ 
        onSubmit,
        removeLastTag: () => {
          if (taggedFiles.length > 0) {
            onRemoveFile(taggedFiles.length - 1);
          }
        } 
      }),
      FileDropExtension.configure({
        onFileDrop
      })
    ],
    content,
    editable: !disabled,
    onUpdate: ({ editor }) => {
      onChange(editor.getText());
    },
    editorProps: {
      attributes: {
        class: 'outline-none',
      }
    }
  });
  
  // Update the editor content when files change or a new file is added
  useEffect(() => {
    if (!editor) return;
    
    // Keep track of the files we've already inserted
    const insertedFiles = new Set<string>();
    
    // Check existing file tags in the document
    editor.state.doc.descendants((node) => {
      if (node.type.name === 'fileTag' && node.attrs.filePath) {
        insertedFiles.add(node.attrs.filePath);
      }
    });
    
    // Check if there are any files that haven't been inserted yet
    const filesToInsert = taggedFiles.filter(file => !insertedFiles.has(file));
    
    // Insert these files at the cursor position
    if (filesToInsert.length > 0) {
      // Get the current cursor position (or the start if none)
      const { selection } = editor.state;
      const pos = selection.empty ? selection.from : selection.from;
      
      // Insert each file as a node
      filesToInsert.forEach(filePath => {
        const node = Node.fromJSON(editor.schema, {
          type: 'fileTag',
          attrs: {
            filePath,
            id: `file-${Date.now()}-${Math.random().toString(36).slice(2, 7)}`
          } as FileTagAttrs
        });
        
        editor.commands.insertContentAt(pos, node);
      });
    }
  }, [taggedFiles, editor]);
  
  // Set placeholder based on state
  useEffect(() => {
    if (editor) {
      editor.setOptions({
        editorProps: {
          attributes: {
            'data-placeholder': placeholder,
            class: 'outline-none'
          }
        }
      });
    }
  }, [editor, placeholder]);
  
  return (
    <div 
      className={cn(
        "min-h-[60px] max-h-[200px] overflow-auto p-3 rounded-md border focus-within:ring-2 focus-within:ring-ring focus-within:ring-primary relative",
        isDragging && "border-2 border-dashed border-primary bg-primary/10",
        disabled && "cursor-not-allowed opacity-50",
        "prose prose-sm max-w-none",
        className
      )}
      data-drag-active={isDragging}
    >
      <EditorContent editor={editor} />
      {editor?.isEmpty && !taggedFiles.length && (
        <div className="absolute top-[50%] left-[14px] transform -translate-y-[50%] pointer-events-none text-muted-foreground">
          {placeholder}
        </div>
      )}
    </div>
  );
};

export default TipTapEditor;