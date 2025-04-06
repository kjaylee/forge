import React, { useRef, useMemo } from 'react';
import { SpecialContent } from './SpecialContent';
import { CodeSection } from './CodeSection';
import { Separator } from "@/components/ui/separator";

interface ConversationSectionProps {
  userMessage: {
    id: string;
    content: string;
    timestamp: Date;
  } | null;
  responseMessages: {
    id: string;
    content: string;
    timestamp: Date;
    isShowUserMessage?: boolean;
  }[];
  isLatest: boolean;
}

const ConversationSection: React.FC<ConversationSectionProps> = ({ 
  userMessage, 
  responseMessages, 
  isLatest
}) => {
  const sectionRef = useRef<HTMLDivElement>(null);
  
  // Process special tags in response content
  const processedContent = useMemo(() => {
    // Check if we have any show_user messages
    const hasShowUserMessages = responseMessages.some(msg => msg.isShowUserMessage);
    
    // If we have show_user messages, only use those and filter out regular system messages
    const messagesToUse = hasShowUserMessages 
      ? responseMessages.filter(msg => msg.isShowUserMessage)
      : responseMessages;
    
    // Combine all relevant messages
    const combinedContent = messagesToUse
      .map(msg => msg.content)
      .join('')
      .trim();
      
    return combinedContent;
  }, [responseMessages]);
  
  // Extract and process special tags
  const { 
    mainContent,
    specialBlocks
  } = useMemo(() => {
    const blocks: { type: string; content: string }[] = [];
    let content = processedContent;
    
    // Extract special tag content
    const tagPatterns = [
      { tag: 'analysis', pattern: /<analysis>([\s\S]*?)<\/analysis>/g },
      { tag: 'thinking', pattern: /<thinking>([\s\S]*?)<\/thinking>/g },
      { tag: 'action_plan', pattern: /<action_plan>([\s\S]*?)<\/action_plan>/g },
      { tag: 'execution', pattern: /<execution>([\s\S]*?)<\/execution>/g },
      { tag: 'verification', pattern: /<verification>([\s\S]*?)<\/verification>/g }
    ];
    
    // Extract and remove special blocks
    tagPatterns.forEach(({ tag, pattern }) => {
      content = content.replace(pattern, (match, p1) => {
        blocks.push({ type: tag, content: p1.trim() });
        return ''; // Remove the tag content from the main text
      });
    });
    
    // Clean up extra newlines
    content = content.replace(/\n{3,}/g, '\n\n').trim();
    
    return {
      mainContent: content,
      specialBlocks: blocks
    };
  }, [processedContent]);
  
  if (!userMessage && responseMessages.length === 0) {
    return null;
  }
  
  return (
    <div ref={sectionRef} className="document-section mb-8 animate-in fade-in duration-300">
      {/* User query section */}
      {userMessage && (
        <div className="user-query mb-4">
          <h3 className="text-base font-semibold text-primary mb-1">User Query</h3>
          <div className="user-content pl-1 whitespace-pre-wrap">
            {userMessage.content}
          </div>
        </div>
      )}
      
      {/* Response section */}
      {responseMessages.length > 0 && (
        <div className="ai-response mb-2">
          <h3 className="text-base font-semibold text-secondary mb-2">Response</h3>
          
          {/* Main response content */}
          <div className="response-content pl-1">
            <CodeSection content={mainContent} />
          </div>
          
          {/* Special content blocks */}
          {specialBlocks.map((block, idx) => (
            <SpecialContent 
              key={`${block.type}-${idx}`} 
              type={block.type} 
              content={block.content} 
            />
          ))}
        </div>
      )}
      
      {!isLatest && <Separator className="mt-8 mb-4" />}
    </div>
  );
};

export default ConversationSection;