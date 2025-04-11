// Types related to file system operations
export interface File {
  path: string;
  is_dir: boolean;
}

// Re-export all types
export * from "./File";
