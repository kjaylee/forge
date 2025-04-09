import React, { useEffect } from 'react';
import { 
  FolderOpen,
  RefreshCw,
  AlertCircle,
  Loader2
} from 'lucide-react';
import { useDirectoryStore } from '@/stores/DirectoryStore';
import { useProjectStore } from '@/stores/ProjectStore';
import TreeItem from './TreeItem';
import { ScrollArea } from './ui/scroll-area';
import { Button } from './ui/button';

const DirectoryView: React.FC = () => {
  const { directoryTree, isLoading, error, loadDirectoryStructure } = useDirectoryStore();
  const { currentProject } = useProjectStore();

  // Load directory structure when the component mounts or when project changes
  useEffect(() => {
    if (currentProject && currentProject.path) {
      loadDirectoryStructure(currentProject.path);
    }
  }, [currentProject?.path, loadDirectoryStructure]);

  // Function to handle refresh button click
  const handleRefresh = () => {
    if (currentProject && currentProject.path) {
      loadDirectoryStructure(currentProject.path);
    }
  };

  // Render empty state if no project is selected
  if (!currentProject) {
    return (
      <div className="flex flex-col h-full">
        <div className="p-3 border-b border-border/50 flex items-center justify-between">
          <div className="font-medium">Project Files</div>
        </div>
        <div className="flex-1 flex items-center justify-center text-muted-foreground text-sm p-4">
          <div className="text-center">
            <FolderOpen className="h-8 w-8 mx-auto mb-2 opacity-50" />
            <p>No project selected</p>
          </div>
        </div>
      </div>
    );
  }

  // Render loading state
  if (isLoading) {
    return (
      <div className="flex flex-col h-full">
        <div className="p-3 border-b border-border/50 flex items-center justify-between">
          <div className="font-medium">Project Files</div>
        </div>
        <div className="flex-1 flex items-center justify-center text-muted-foreground text-sm p-4">
          <div className="text-center">
            <Loader2 className="h-8 w-8 mx-auto mb-2 animate-spin" />
            <p>Loading directory structure...</p>
          </div>
        </div>
      </div>
    );
  }

  // Render error state
  if (error) {
    return (
      <div className="flex flex-col h-full">
        <div className="p-3 border-b border-border/50 flex items-center justify-between">
          <div className="font-medium">Project Files</div>
          <Button variant="ghost" size="sm" onClick={handleRefresh}>
            <RefreshCw className="h-4 w-4" />
          </Button>
        </div>
        <div className="flex-1 flex items-center justify-center text-destructive text-sm p-4">
          <div className="text-center">
            <AlertCircle className="h-8 w-8 mx-auto mb-2" />
            <p>Error loading files:</p>
            <p className="mt-2 max-w-xs break-words">{error}</p>
          </div>
        </div>
      </div>
    );
  }

  // Render empty directory structure
  if (!directoryTree) {
    return (
      <div className="flex flex-col h-full">
        <div className="p-3 border-b border-border/50 flex items-center justify-between">
          <div className="font-medium">Project Files</div>
          <Button variant="ghost" size="sm" onClick={handleRefresh}>
            <RefreshCw className="h-4 w-4" />
          </Button>
        </div>
        <div className="flex-1 flex items-center justify-center text-muted-foreground text-sm p-4">
          <div className="text-center">
            <FolderOpen className="h-8 w-8 mx-auto mb-2 opacity-50" />
            <p>No files found</p>
          </div>
        </div>
      </div>
    );
  }

  // Render directory tree
  return (
    <div className="flex flex-col h-full">
      <div className="p-3 border-b border-border/50 flex items-center justify-between">
        <div className="font-medium">Project Files</div>
        <Button variant="ghost" size="sm" onClick={handleRefresh}>
          <RefreshCw className="h-4 w-4" />
        </Button>
      </div>
      <ScrollArea className="flex-1">
        <div className="p-2">
          <TreeItem item={directoryTree} level={0} />
        </div>
      </ScrollArea>
    </div>
  );
};

export default DirectoryView;