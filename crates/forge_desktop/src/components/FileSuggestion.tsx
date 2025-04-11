import React from "react";
import { File } from "@/types";
import { cn } from "@/utils/utils";
import { FileIcon, Folder } from "lucide-react";

interface FileSuggestionProps {
  suggestions: File[];
  query: string;
  onSelect: (filePath: string) => void;
  onClose: () => void;
}

const FileSuggestion: React.FC<FileSuggestionProps> = ({
  suggestions,
  query,
  onSelect,
  onClose,
}) => {
  const [selectedIndex, setSelectedIndex] = React.useState(0);

  // Filter suggestions based on query
  const filteredSuggestions = suggestions
    .filter((file) => file.path.toLowerCase().includes(query.toLowerCase()))
    .slice(0, 10); // Limit to 10 results for performance

  // Debug logs
  React.useEffect(() => {
    console.log("FileSuggestion component rendered");
    console.log("Query:", query);
    console.log("Filtered suggestions:", filteredSuggestions);
  }, [query, filteredSuggestions]);

  // Keyboard navigation
  React.useEffect(() => {
    const handleKeyDown = (event: KeyboardEvent) => {
      console.log("Key pressed in suggestion component:", event.key);

      switch (event.key) {
        case "ArrowDown":
          event.preventDefault();
          setSelectedIndex((prevIndex) =>
            prevIndex < filteredSuggestions.length - 1 ? prevIndex + 1 : 0,
          );
          break;

        case "ArrowUp":
          event.preventDefault();
          setSelectedIndex((prevIndex) =>
            prevIndex > 0 ? prevIndex - 1 : filteredSuggestions.length - 1,
          );
          break;

        case "Enter":
          event.preventDefault();
          if (filteredSuggestions[selectedIndex]) {
            onSelect(filteredSuggestions[selectedIndex].path);
          }
          break;

        case "Escape":
          event.preventDefault();
          onClose();
          break;
      }
    };

    window.addEventListener("keydown", handleKeyDown);
    return () => window.removeEventListener("keydown", handleKeyDown);
  }, [filteredSuggestions, selectedIndex, onSelect, onClose]);

  // No suggestions, don't render anything
  if (filteredSuggestions.length === 0) {
    return (
      <div className="p-2 text-sm text-muted-foreground">No matching files</div>
    );
  }

  // Helper to get just the filename part of a path
  const getBasename = (path: string): string => {
    const parts = path.split(/[/\\]/); // Split by both forward and backslashes
    return parts[parts.length - 1] || path;
  };

  return (
    <div className="bg-popover border border-border rounded-md shadow-md overflow-hidden w-64 max-h-[300px] overflow-y-auto">
      <div className="p-1">
        {filteredSuggestions.map((file, index) => (
          <div
            key={file.path}
            onClick={() => onSelect(file.path)}
            className={cn(
              "flex items-center gap-2 px-2 py-1.5 text-sm rounded cursor-pointer",
              selectedIndex === index
                ? "bg-accent text-accent-foreground"
                : "hover:bg-muted",
            )}
            onMouseEnter={() => setSelectedIndex(index)}
          >
            <span className="flex-shrink-0">
              {file.is_dir ? (
                <Folder className="h-4 w-4" />
              ) : (
                <FileIcon className="h-4 w-4" />
              )}
            </span>
            <span className="truncate">{getBasename(file.path)}</span>
          </div>
        ))}
      </div>
    </div>
  );
};

export default FileSuggestion;
