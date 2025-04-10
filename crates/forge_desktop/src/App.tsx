import { useForgeStore } from "@/stores/ForgeStore";
import { useProjectStore } from "@/stores/ProjectStore";
import { useDirectoryStore } from "@/stores/DirectoryStore";
import ProjectSelectionView from "@/components/ProjectSelectionView";
import ConversationHeader from "@/components/ConversationHeader";
import ModeSwitcher from "@/components/ModeSwitcher";
import DocumentView from "@/components/DocumentView";
import ToolConsoleView from "@/components/ToolConsoleView";
import MessageInput from "@/components/MessageInput";
import StatusBar from "@/components/StatusBar";
import DirectoryView from "@/components/DirectoryView";
import { TooltipProvider } from "@/components/ui/tooltip";
import { PanelLeft } from "lucide-react";
import { useEffect, useState } from "react";
import {
  ResizableHandle,
  ResizablePanel,
  ResizablePanelGroup
} from "@/components/ui/resizable";
import { Button } from "@/components/ui/button";
import { ClerkProvider, SignedIn, SignedOut } from "@clerk/clerk-react";
import { BrowserRouter, Navigate, Route, Routes } from "react-router-dom";
import { Toaster } from 'sonner';

import { LoginPage } from "./components/Login";
import { SignUpPage } from "./components/SignUp";
import { InvitationPage } from "./components/Invitation";
import { LoadingScreen } from "./components/LoadingScreen";
import { InvitedOnly } from "./components/InvitedOnly";
import { WaitListed } from "./components/WaitListed";

// Component for the chat interface
const ChatInterface: React.FC = () => {
  useEffect(() => {
    const forgeStore = useForgeStore.getState();
    if (!forgeStore.listenersInitialized) {
      forgeStore.setupListeners();
    }
  }, []);

  // Initialize sizes from localStorage or use defaults
  const [directorySize, setDirectorySize] = useState(() => {
    return Number(localStorage.getItem('directorySize')) || 20;
  });
  const [toolConsoleSize, setToolConsoleSize] = useState(() => {
    return Number(localStorage.getItem('toolConsoleSize')) || 25;
  });

  const { isVisible, toggleVisible } = useDirectoryStore();

  // Persist sizes to localStorage
  useEffect(() => {
    localStorage.setItem('directorySize', directorySize.toString());
  }, [directorySize]);

  useEffect(() => {
    localStorage.setItem('toolConsoleSize', toolConsoleSize.toString());
  }, [toolConsoleSize]);

  return (
    <div className="flex flex-col h-screen w-full overflow-hidden bg-background text-foreground antialiased">
      <div className="sticky top-0 z-10">
        <ConversationHeader />
      </div>

      <ResizablePanelGroup direction="horizontal" className="flex-1">
        {/* Directory Panel - Only shown when visible */}
        {isVisible && (
          <>
            <ResizablePanel
              defaultSize={directorySize}
              minSize={15}
              maxSize={40}
              onResize={(size) => setDirectorySize(Math.round(size))}
              className="border-r border-border/40"
            >
              <DirectoryView />
            </ResizablePanel>
            <ResizableHandle withHandle />
          </>
        )}

        {/* Main Content Panel - Flexes to fill remaining space */}
        <ResizablePanel
          defaultSize={isVisible ? 100 - directorySize - toolConsoleSize : 100 - toolConsoleSize}
          minSize={35}
          className="flex-1"
        >
          <div className="flex flex-col h-full">
            <div className="sticky top-0 z-10 bg-background/95 backdrop-blur-sm border-b border-border/50 flex items-center">
              <Button
                variant="ghost"
                size="icon"
                className="p-2 mr-1 hover:bg-accent/50 rounded-md"
                onClick={toggleVisible}
                title={isVisible ? "Hide directory panel" : "Show directory panel"}
              >
                <PanelLeft className={`h-5 w-5 ${isVisible ? 'text-primary' : 'text-muted-foreground'}`} />
              </Button>
              <ModeSwitcher />
            </div>
            <div className="flex-1 overflow-hidden relative">
              <DocumentView />
            </div>
            <MessageInput />
          </div>
        </ResizablePanel>

        <ResizableHandle withHandle />

        {/* Tool Console Panel - Maintains fixed size */}
        <ResizablePanel
          defaultSize={toolConsoleSize}
          minSize={20}
          maxSize={50}
          onResize={(size) => setToolConsoleSize(Math.round(size))}
          className="border-l border-border/40"
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
    <ClerkProvider
      afterSignOutUrl="/sign-in"
      signUpUrl="/sign-up"
      signInUrl="/sign-in"
      signInForceRedirectUrl="/"
      signUpForceRedirectUrl="/"
      publishableKey={import.meta.env.VITE_CLERK_PUBLISHABLE_KEY}>
      <TooltipProvider>
        <BrowserRouter>
          <SignedOut>
            <Routes>
              <Route path="/sign-in" element={<LoginPage />} />
              <Route path="/sign-up" element={<SignUpPage />} />
              <Route path="/*" element={<Navigate to="/sign-in" replace />} />
            </Routes>
          </SignedOut>
          <SignedIn>
            <InvitedOnly>
              <Routes>
                <Route path="/*" element={<AppContent />} />
              </Routes>
            </InvitedOnly>
            <WaitListed>
              <Routes>
                <Route path="/*" element={<InvitationPage />} />
              </Routes>
            </WaitListed>
          </SignedIn>
        </BrowserRouter>
      </TooltipProvider>
      <Toaster richColors position="top-right" />
    </ClerkProvider>
  );
}

export default App;