import { ForgeProvider } from "@/contexts/ForgeContext";
import { ProjectProvider, useProject } from "@/contexts/ProjectContext";
import ProjectSelectionView from "@/components/ProjectSelectionView";
import ConversationHeader from "@/components/ConversationHeader";
import ModeSwitcher from "@/components/ModeSwitcher";
import ChatView from "@/components/ChatView";
import MessageInput from "@/components/MessageInput";
import StatusBar from "@/components/StatusBar";
import { TooltipProvider } from "@/components/ui/tooltip";
import { Loader2 } from "lucide-react";

// Component for the loading screen
const LoadingScreen: React.FC = () => (
  <div className="h-screen w-full flex flex-col items-center justify-center">
    <Loader2 className="h-12 w-12 animate-spin text-primary mb-4" />
    <p className="text-muted-foreground">Loading...</p>
  </div>
);

// Component for the chat interface
const ChatInterface: React.FC = () => {
  return (
    <div className="flex flex-col h-screen w-full overflow-hidden bg-background font-sans text-foreground antialiased">
      <div className="sticky top-0 z-10">
        <ConversationHeader />
      </div>
      <div className="flex-1 flex flex-col overflow-hidden border-x border-border/40 mx-auto w-full max-w-6xl shadow-sm">
        <div className="sticky top-0 z-10 bg-background/95 backdrop-blur-sm border-b border-border/50">
          <ModeSwitcher />
        </div>
        <div className="flex-1 overflow-hidden relative">
          <ChatView />
        </div>
        <MessageInput />
      </div>
      <StatusBar />
    </div>
  );
};

// Main app wrapper with conditional rendering
const AppContent: React.FC = () => {
  const { currentProject, isLoading } = useProject();
  
  // Show loading screen during initial load or project switching
  if (isLoading) {
    return <LoadingScreen />;
  }
  
  // Show project selection if no project is selected
  if (!currentProject) {
    return <ProjectSelectionView />;
  }
  
  // Show chat interface when a project is selected
  return <ChatInterface />;
};

function App() {
  return (
    <ProjectProvider>
      <ForgeProvider>
        <TooltipProvider>
          <AppContent />
        </TooltipProvider>
      </ForgeProvider>
    </ProjectProvider>
  );
}

export default App;