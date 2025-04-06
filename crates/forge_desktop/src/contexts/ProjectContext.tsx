// This context provides project management state and functionality to React components

import React, { createContext, useContext, useState, useEffect, useCallback, ReactNode } from 'react';
import { invoke } from '@tauri-apps/api/core';
import { open } from '@tauri-apps/plugin-dialog';

// Type definitions for projects
export interface ProjectInfo {
  path: string;
  name: string;
  lastAccessed: string; // ISO timestamp
}

interface ProjectContextType {
  currentProject: ProjectInfo | null;
  recentProjects: ProjectInfo[];
  isLoading: boolean;
  error: string | null;
  selectProject: (path?: string) => Promise<void>;
  switchProject: (projectInfo: ProjectInfo) => Promise<void>;
  createNewProject: (path: string, name?: string) => Promise<void>;
  closeProject: () => Promise<void>;
  refreshProjects: () => Promise<void>;
  openDirectoryDialog: () => Promise<string | undefined>;
}

// Create the context with default values
const ProjectContext = createContext<ProjectContextType>({
  currentProject: null,
  recentProjects: [],
  isLoading: false,
  error: null,
  selectProject: async () => {},
  switchProject: async () => {},
  createNewProject: async () => {},
  closeProject: async () => {},
  refreshProjects: async () => {},
  openDirectoryDialog: async () => undefined,
});

// Context provider component
export const ProjectProvider: React.FC<{ children: ReactNode }> = ({ children }) => {
  const [currentProject, setCurrentProject] = useState<ProjectInfo | null>(null);
  const [recentProjects, setRecentProjects] = useState<ProjectInfo[]>([]);
  const [isLoading, setIsLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  
  // Load project state at startup
  useEffect(() => {
    const loadProjects = async () => {
      try {
        setIsLoading(true);
        await invoke('load_projects_state');
        await refreshProjects();
        setIsLoading(false);
      } catch (err) {
        setError(err instanceof Error ? err.message : String(err));
        setIsLoading(false);
      }
    };

    loadProjects();
  }, []);
  
  // Refresh project state from backend
  const refreshProjects = useCallback(async () => {
    try {
      setIsLoading(true);
      setError(null);
      
      // Get current project
      const project = await invoke<ProjectInfo | null>('get_current_project');
      setCurrentProject(project);
      
      // Get recent projects
      const projects = await invoke<ProjectInfo[]>('get_recent_projects');
      setRecentProjects(projects);
      
      setIsLoading(false);
    } catch (err) {
      setError(err instanceof Error ? err.message : String(err));
      setIsLoading(false);
    }
  }, []);
  
  // Select a project
  const selectProject = useCallback(async (path?: string) => {
    try {
      setIsLoading(true);
      setError(null);
      
      // If no path provided, open directory dialog
      const directoryPath = path || await openDirectoryDialog();
      
      if (!directoryPath) {
        setIsLoading(false);
        return; // User cancelled
      }
      
      // Select the project
      const projectInfo = await invoke<ProjectInfo>('select_project', {
        path: directoryPath,
        name: undefined, // Let backend determine name from path
      });
      
      setCurrentProject(projectInfo);
      await refreshProjects(); // Refresh recent projects list
      setIsLoading(false);
    } catch (err) {
      setError(err instanceof Error ? err.message : String(err));
      setIsLoading(false);
      throw err; // Re-throw for caller to handle
    }
  }, [refreshProjects]);
  
  // Switch to a different project
  const switchProject = useCallback(async (projectInfo: ProjectInfo) => {
    try {
      setIsLoading(true);
      setError(null);
      
      // Switch to the project
      const updatedProject = await invoke<ProjectInfo>('switch_project', {
        path: projectInfo.path,
      });
      
      setCurrentProject(updatedProject);
      await refreshProjects(); // Refresh recent projects list
      setIsLoading(false);
    } catch (err) {
      setError(err instanceof Error ? err.message : String(err));
      setIsLoading(false);
      throw err;
    }
  }, [refreshProjects]);
  
  // Create a new project
  const createNewProject = useCallback(async (path: string, name?: string) => {
    try {
      setIsLoading(true);
      setError(null);
      
      // Create the project
      const projectInfo = await invoke<ProjectInfo>('create_new_project', {
        path,
        name,
      });
      
      setCurrentProject(projectInfo);
      await refreshProjects(); // Refresh recent projects list
      setIsLoading(false);
    } catch (err) {
      setError(err instanceof Error ? err.message : String(err));
      setIsLoading(false);
      throw err;
    }
  }, [refreshProjects]);
  
  // Close the current project
  const closeProject = useCallback(async () => {
    try {
      setIsLoading(true);
      setError(null);
      
      // Close the project
      await invoke('close_current_project');
      
      setCurrentProject(null);
      await refreshProjects(); // Refresh recent projects list
      setIsLoading(false);
    } catch (err) {
      setError(err instanceof Error ? err.message : String(err));
      setIsLoading(false);
      throw err;
    }
  }, [refreshProjects]);
  
  // Open directory dialog
  const openDirectoryDialog = useCallback(async (): Promise<string | undefined> => {
    try {
      // Open directory selection dialog
      const result = await open({
        directory: true,
        multiple: false,
        title: 'Select Project Directory',
      });
      
      // Return the selected directory or undefined if cancelled
      return typeof result === 'string' ? result : undefined;
    } catch (err) {
      setError(err instanceof Error ? err.message : String(err));
      return undefined;
    }
  }, []);
  
  // The context value
  const contextValue: ProjectContextType = {
    currentProject,
    recentProjects,
    isLoading,
    error,
    selectProject,
    switchProject,
    createNewProject,
    closeProject,
    refreshProjects,
    openDirectoryDialog,
  };

  return (
    <ProjectContext.Provider value={contextValue}>
      {children}
    </ProjectContext.Provider>
  );
};

// Hook for using the Project context
export const useProject = () => useContext(ProjectContext);