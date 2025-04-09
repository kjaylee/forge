import React, { useEffect, FormEvent } from 'react';
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
  onSubmit: (e?: FormEvent) => void | Promise<void>;
  taggedFiles: string[];
  onRemoveFile: (index: number) => void;
  onFileDrop: (path: string) => void;
  disabled?: boolean;
  isDragging: boolean;
  placeholder?: string;
  className?: string;
  setTaggedFiles?: (files: string[]) => void;
}

// Create SubmitExtension to handle Enter for submission
const SubmitExtension = Extension.create({
  name: 'submitExtension',
  
  addProseMirrorPlugins() {
    const onSubmit = this.options.onSubmit;
    const removeLastTag = this.options.removeLastTag;
    
    return [
      new Plugin({
        key: new PluginKey('submitExtension'),
        props: {
          handleKeyDown(_view, event) {
            if (event.key === 'Enter' && !event.shiftKey) {
              event.preventDefault();
              if (onSubmit) onSubmit();
              return true;
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
            dragover(_, event) {
              // Make sure we can handle this drop
              if (event.dataTransfer && event.dataTransfer.types.includes('text/plain')) {
                event.preventDefault();
                return true;
              }
              return false;
            },
            drop(_, event) {
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
  className,
  setTaggedFiles
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
      FileTagNode.configure({
        onRemove: () => {
          // When a file tag is removed from the editor,
          // we need to update the store state
          if (setTaggedFiles && editor) {
            // Get all remaining tags from the editor
            const remainingTags: string[] = [];
            editor.state.doc.descendants((node) => {
              if (node.type.name === 'fileTag' && node.attrs.filePath) {
                remainingTags.push(node.attrs.filePath);
              }
            });
            // Update the store with the current tags in the editor
            setTaggedFiles(remainingTags);
          }
        }
      }),
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
  
  // Helper function to compare arrays of strings
  const arraysEqual = (a: string[], b: string[]): boolean => {
    if (a.length !== b.length) return false;
    return a.every((val, index) => val === b[index]);
  };

  // Update the editor when taggedFiles changes from external sources
  useEffect(() => {
    if (!editor) return;
    
    // Extract all file tags currently in the document
    const extractTagsFromEditor = (): string[] => {
      const currentTags: string[] = [];
      editor.state.doc.descendants((node) => {
        if (node.type.name === 'fileTag' && node.attrs.filePath) {
          currentTags.push(node.attrs.filePath);
        }
      });
      return currentTags;
    };
    
    // Compare current editor tags with the taggedFiles prop
    const currentTags = extractTagsFromEditor();
    
    // If editor tags don't match the store's tags, sync them
    if (!arraysEqual(currentTags, taggedFiles)) {
      // Find new tags to add (in taggedFiles but not in editor)
      const tagsToAdd = taggedFiles.filter(file => !currentTags.includes(file));
      
      if (tagsToAdd.length > 0) {
        // Get the current cursor position
        const { selection } = editor.state;
        const pos = selection.empty ? selection.from : selection.from;
        
        // Insert each new tag at the cursor position
        tagsToAdd.forEach(tagPath => {
          const node = Node.fromJSON(editor.schema, {
            type: 'fileTag',
            attrs: {
              filePath: tagPath,
              id: `file-${Date.now()}-${Math.random().toString(36).slice(2, 7)}`
            } as FileTagAttrs
          });
          
          editor.commands.insertContentAt(pos, node);
        });
      }
    }
  }, [taggedFiles, editor]);
  
  // Set placeholder based on state
  useEffect(() => {
    if (!editor) return;
    
    editor.setOptions({
      editorProps: {
        attributes: {
          'data-placeholder': placeholder,
          class: 'outline-none'
        }
      }
    });
  }, [editor, placeholder]);
  
  // Add a transaction handler to keep taggedFiles synced with editor state
  useEffect(() => {
    if (!editor || !setTaggedFiles) return;
    
    const updateTagsFromEditor = () => {
      const currentTags: string[] = [];
      editor.state.doc.descendants((node) => {
        if (node.type.name === 'fileTag' && node.attrs.filePath) {
          currentTags.push(node.attrs.filePath);
        }
      });
      
      // Only update if the tags have changed
      if (!arraysEqual(currentTags, taggedFiles)) {
        setTaggedFiles(currentTags);
      }
    };
    
    // Listen for transaction changes
    editor.on('transaction', updateTagsFromEditor);
    
    return () => {
      editor.off('transaction', updateTagsFromEditor);
    };
  }, [editor, taggedFiles, setTaggedFiles]);
  
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