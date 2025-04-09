import React from 'react';
import { CodeBlock } from "./CodeBlock";
import { extractCodeBlocks, extractFilePath } from "@/lib/utils";
import ReactMarkdown from 'react-markdown';

interface CodeSectionProps {
  content: string;
}

export const CodeSection: React.FC<CodeSectionProps> = ({ content }) => {
  // Extract code blocks from the content
  const codeBlocks = extractCodeBlocks(content);
  
  if (codeBlocks.length === 0) {
    // If no code blocks found, just render content as markdown
    return (
      <div className="prose prose-sm dark:prose-invert max-w-none">
        <ReactMarkdown>{content}</ReactMarkdown>
      </div>
    );
  }
  
  // Function to render content with code blocks highlighted
  const renderContentWithCodeBlocks = () => {
    // Replace code blocks with placeholders for later replacement
    let processedContent = content;
    const placeholders: { placeholder: string; component: React.ReactNode }[] = [];
    
    codeBlocks.forEach((block, index) => {
      const blockPattern = new RegExp('```' + block.language + '\\n' + block.code.replace(/[.*+?^${}()|[\]\\]/g, '\\$&') + '```', 'g');
      const placeholder = `__CODE_BLOCK_${index}__`;
      processedContent = processedContent.replace(blockPattern, placeholder);
      
      // Extract file path from any header above the code block
      const contentBeforeBlock = content.split('```' + block.language)[index];
      let filePath = null;
      
      if (contentBeforeBlock) {
        // Look for file path in the last 3 lines before the code block
        const lines = contentBeforeBlock.split('\n');
        const lastLines = lines.slice(-3).join('\n');
        filePath = extractFilePath(lastLines);
      }
      
      placeholders.push({
        placeholder,
        component: (
          <div key={index} className="my-4">
            <CodeBlock 
              code={block.code} 
              language={block.language} 
              fileName={filePath}
            />
          </div>
        )
      });
    });
    
    // Split content by placeholders and reconstruct with actual components
    const parts = processedContent.split(/(\_\_CODE\_BLOCK\_\d+\_\_)/g);
    return parts.map((part, i) => {
      // Check if this part is a placeholder
      const placeholderMatch = part.match(/\_\_CODE\_BLOCK\_(\d+)\_\_/);
      if (placeholderMatch) {
        const index = parseInt(placeholderMatch[1]);
        return placeholders[index].component;
      }
      // Otherwise, render as markdown
      return part ? (
        <div key={i} className="prose prose-sm dark:prose-invert max-w-none">
          <ReactMarkdown>{part}</ReactMarkdown>
        </div>
      ) : null;
    });
  };
  
  return <>{renderContentWithCodeBlocks()}</>;
};