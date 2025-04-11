import { useForgeStore } from "@/stores/ForgeStore";
import { useProjectStore } from "@/stores/ProjectStore";
import ProjectSelectionView from "@/components/ProjectSelectionView";
import ConversationHeader from "@/components/ConversationHeader";
import ModeSwitcher from "@/components/ModeSwitcher";
import DocumentView from "@/components/DocumentView";
import MessageInput from "@/components/MessageInput";
import StatusBar from "@/components/StatusBar";
import FileViewer from "@/components/FileViewerModal";
import { TooltipProvider } from "@/components/ui/tooltip";
import { ThemeProvider } from "next-themes";
import { Loader2 } from "lucide-react";
import { useEffect } from "react";
// Component for the loading screen
const LoadingScreen: React.FC = () => (
  <div className="h-screen w-full flex flex-col items-center justify-center">
    <Loader2 className="h-12 w-12 animate-spin text-primary mb-4" />
    <p className="text-muted-foreground">Loading...</p>
  </div>
);

// Component for the chat interface
const ChatInterface: React.FC = () => {
  useEffect(() => {
    const forgeStore = useForgeStore.getState();
    if (!forgeStore.listenersInitialized) {
      forgeStore.setupListeners();
    }
  }, []);

  return (
    <div className="flex flex-col h-screen w-full overflow-hidden bg-background text-foreground antialiased">
      <div className="sticky top-0 z-10">
        <ConversationHeader />
      </div>
      <div className="flex flex-col h-full">
        <div className="sticky top-0 z-10 bg-background/95 backdrop-blur-sm border-b border-border/50 flex items-center">
          <ModeSwitcher />
        </div>
        <div className="flex-1 overflow-hidden relative">
          <DocumentView />
        </div>
        <MessageInput />
      </div>

      <StatusBar />
    </div>
  );
};

// Main app wrapper with conditional rendering
const AppContent: React.FC = () => {
  const { currentProject, isLoading } = useProjectStore();

  if (isLoading) {
    return <LoadingScreen />;
  }

  if (!currentProject) {
    return <ProjectSelectionView />;
  }

  return <ChatInterface />;
};

function App() {
  return (
    <ThemeProvider attribute="class">
      <TooltipProvider>
        <AppContent />
        <FileViewer />
      </TooltipProvider>
    </ThemeProvider>
  );
}

export default App;
