import React from "react";
import { File } from "@/types";
import { cn } from "@/utils/utils";
import { FileIcon } from "lucide-react";

interface FileSuggestionProps {
  suggestions: File[];
  query: string;
  onSelect: (filePath: string) => void;
  onClose: () => void;
}

// Highlight helper: returns [pre, match, post] spans
function getHighlightedParts(text: string, query: string): React.ReactNode {
  if (!query) return text;
  const queryLower = query.toLowerCase();
  const textLower = text.toLowerCase();
  const matchIndex = textLower.indexOf(queryLower);
  if (matchIndex === -1) return text;
  const pre = text.slice(0, matchIndex);
  const match = text.slice(matchIndex, matchIndex + query.length);
  const post = text.slice(matchIndex + query.length);
  return (
    <>
      {pre}
      <span className="bg-accent/50 text-accent-foreground font-semibold rounded-sm px-0.5">{match}</span>
      {post}
    </>
  );
}

const FileSuggestion: React.FC<FileSuggestionProps> = ({
  suggestions,
  query,
  onSelect,
  onClose,
}) => {
  const [selectedIndex, setSelectedIndex] = React.useState(0);

  const queryLower = query.toLowerCase();

  // Helper to get base name (filename)
  const getBaseName = (path: string) => {
    if (!path) return "";
    const parts = path.split("/");
    return parts[parts.length - 1];
  };

  // Only consider actual files (not directories)
  const fileOnly = suggestions.filter(f => !f.is_dir);

  // Exact match (very rare except for full, but more relevant)
  const exactMatches = fileOnly.filter(f => getBaseName(f.path).toLowerCase() === queryLower);
  // Prefix matches for the filename
  const prefixMatches = fileOnly.filter(
    f => getBaseName(f.path).toLowerCase().startsWith(queryLower) &&
         getBaseName(f.path).toLowerCase() !== queryLower
  );
  // Substring (non-prefix, non-exact) matches in basename
  const substringMatches = fileOnly.filter(
    f => getBaseName(f.path).toLowerCase().includes(queryLower) &&
         !getBaseName(f.path).toLowerCase().startsWith(queryLower)
  );

  // Combine and alphabetize each group by relative path
  const allSuggestions = [
    ...exactMatches.sort((a, b) => a.path.localeCompare(b.path)),
    ...prefixMatches.sort((a, b) => a.path.localeCompare(b.path)),
    ...substringMatches.sort((a, b) => a.path.localeCompare(b.path)),
  ].slice(0, 30);

  // Keyboard navigation
  React.useEffect(() => {
    const handleKeyDown = (event: KeyboardEvent) => {
      switch (event.key) {
        case "ArrowDown":
          event.preventDefault();
          setSelectedIndex((prevIndex) =>
            prevIndex < allSuggestions.length - 1 ? prevIndex + 1 : 0,
          );
          break;
        case "ArrowUp":
          event.preventDefault();
          setSelectedIndex((prevIndex) =>
            prevIndex > 0 ? prevIndex - 1 : allSuggestions.length - 1,
          );
          break;
        case "Enter":
          event.preventDefault();
          if (allSuggestions[selectedIndex]) {
            onSelect(allSuggestions[selectedIndex].path);
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
  }, [allSuggestions, selectedIndex, onSelect, onClose]);

  if (allSuggestions.length === 0) {
    return (
      <div className="p-2 text-sm text-muted-foreground">No matching files</div>
    );
  }

  return (
    <div className="bg-popover border border-border rounded-md shadow-md overflow-hidden w-96 max-h-[300px] overflow-y-auto">
      <div className="p-1">
        {allSuggestions.map((file, index) => {
          const base = getBaseName(file.path);
          let highlightPart: React.ReactNode = base;
          if (base.toLowerCase() === queryLower) {
            highlightPart = getHighlightedParts(base, query);
          } else if (base.toLowerCase().startsWith(queryLower)) {
            highlightPart = getHighlightedParts(base, query);
          } else if (base.toLowerCase().includes(queryLower)) {
            highlightPart = getHighlightedParts(base, query);
          }

          return (
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
                <FileIcon className="h-4 w-4" />
              </span>
              <span className="truncate">{highlightPart}</span>
              <span className="truncate text-xs text-muted-foreground ml-2">{file.path}</span>
            </div>
          );
        })}
      </div>
    </div>
  );
};

export default FileSuggestion;
