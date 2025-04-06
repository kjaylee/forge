import { useForgeStore } from "@/stores/ForgeStore";
import { useProjectStore } from "@/stores/ProjectStore";
import ProjectSelectionView from "@/components/ProjectSelectionView";
import ConversationHeader from "@/components/ConversationHeader";
import ModeSwitcher from "@/components/ModeSwitcher";
import DocumentView from "@/components/DocumentView";
import ToolConsoleView from "@/components/ToolConsoleView";
import MessageInput from "@/components/MessageInput";
import StatusBar from "@/components/StatusBar";
import { TooltipProvider } from "@/components/ui/tooltip";
import { Loader2 } from "lucide-react";
import { useEffect, useState } from "react";
import { 
  ResizableHandle, 
  ResizablePanel, 
  ResizablePanelGroup 
} from "@/components/ui/resizable";

// Component for the loading screen
const LoadingScreen: React.FC = () => (
  <div className="h-screen w-full flex flex-col items-center justify-center">
    <Loader2 className="h-12 w-12 animate-spin text-primary mb-4" />
    <p className="text-muted-foreground">Loading...</p>
  </div>
);

// Component for the chat interface
const ChatInterface: React.FC = () => {
  // Initialize forge store listeners when chat interface is mounted
  useEffect(() => {
    // Setup is done automatically in store initialization, this is just for clarity
    const forgeStore = useForgeStore.getState();
    if (!forgeStore.listenersInitialized) {
      forgeStore.setupListeners();
    }
  }, []);
  
  // State for remembering panel sizes
  const [toolConsoleSize, setToolConsoleSize] = useState(25); // 25% default

  return (
    <div className="flex flex-col h-screen w-full overflow-hidden bg-background font-sans text-foreground antialiased">
      <div className="sticky top-0 z-10">
        <ConversationHeader />
      </div>
      
      <ResizablePanelGroup direction="horizontal" className="flex-1 overflow-hidden">
        <ResizablePanel 
          defaultSize={100 - toolConsoleSize} 
          minSize={50}
          onResize={(size) => setToolConsoleSize(100 - size)}
          className="border-x border-border/40 shadow-sm"
        >
          <div className="flex flex-col h-full">
            <div className="sticky top-0 z-10 bg-background/95 backdrop-blur-sm border-b border-border/50">
              <ModeSwitcher />
            </div>
            <div className="flex-1 overflow-hidden relative">
              <DocumentView />
            </div>
            <MessageInput />
          </div>
        </ResizablePanel>
        
        <ResizableHandle withHandle />
        
        <ResizablePanel 
          defaultSize={toolConsoleSize} 
          minSize={15}
          onResize={setToolConsoleSize}
          className="border-r border-border/40"
        >
          <ToolConsoleView />
        </ResizablePanel>
      </ResizablePanelGroup>
      
      <StatusBar />
    </div>
  );
};

// Main app wrapper with conditional rendering
const AppContent: React.FC = () => {
  // Use the project store directly
  const { currentProject, isLoading } = useProjectStore();
  
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
    <TooltipProvider>
      <AppContent />
    </TooltipProvider>
  );
}

export default App;