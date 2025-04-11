import { Extension } from "@tiptap/core";
import { Plugin, PluginKey } from "@tiptap/pm/state";
import { File } from "@/types";
import tippy, { Instance } from "tippy.js";
import FileSuggestion from "./FileSuggestion";
import { createRoot, Root } from "react-dom/client";

// Define interface for the extension options
interface FileSuggestionExtensionOptions {
  onChange: (text: string) => void;
  fetchFileSuggestions: () => Promise<File[]>;
}

// Define the plugin state type
interface FileSuggestionState {
  active: boolean;
  query: string;
  suggestions: File[];
  range: { from: number; to: number };
}

// Plugin key for state management
const FileSuggestionPluginKey = new PluginKey<FileSuggestionState>(
  "fileSuggestion",
);

// Create the extension
const FileSuggestionExtension =
  Extension.create<FileSuggestionExtensionOptions>({
    name: "fileSuggestion",

    addOptions() {
      return {
        onChange: () => {},
        fetchFileSuggestions: async () => [],
      };
    },

    addProseMirrorPlugins() {
      const { onChange, fetchFileSuggestions } = this.options;

      return [
        new Plugin<FileSuggestionState>({
          key: FileSuggestionPluginKey,

          // State management
          state: {
            init(): FileSuggestionState {
              console.log("Initializing FileSuggestionPluginKey state");
              return {
                active: false,
                query: "",
                suggestions: [],
                range: { from: 0, to: 0 },
              };
            },

            apply(tr, prev): FileSuggestionState {
              // Always log the transaction type for debugging
              console.log(
                "Transaction type:",
                tr.docChanged
                  ? "Doc changed"
                  : tr.selectionSet
                    ? "Selection changed"
                    : "Other transaction",
              );

              // Skip if this isn't a doc change transaction
              if (!tr.docChanged) {
                return prev;
              }

              // Check for @ character
              const { selection } = tr;
              const { $from, from } = selection;

              // Get text before cursor - up to 100 chars
              const textBefore = $from.doc.textBetween(
                Math.max(0, from - 100),
                from,
                "\n",
              );

              // Debug log
              console.log("Text before cursor:", textBefore);

              // Check if @ is present and get position
              const atIndex = textBefore.lastIndexOf("@");

              // If @ found (not at the beginning of a line and not part of an email address)
              if (atIndex >= 0) {
                // Check if @ is not part of an email
                const isEmail = /\S+@\S+\.\S+/.test(textBefore);
                if (isEmail) {
                  console.log("Detected @ in email address, ignoring");
                  return { ...prev, active: false };
                }

                // Calculate range for replacement
                const start = from - (textBefore.length - atIndex);
                const end = from;

                // Extract query (text after @)
                const query = textBefore.substring(atIndex + 1);
                console.log("Found @ with query:", query);

                return {
                  active: true,
                  query,
                  range: { from: start, to: end },
                  suggestions: prev.suggestions,
                };
              }

              // No @ found
              return { ...prev, active: false };
            },
          },

          // View management
          view(view) {
            // Container for the popup
            let popup: Instance | null = null;
            let suggestionRoot: Root | null = null;

            console.log("FileSuggestion view initialized");

            // Load suggestions function
            const loadSuggestions = async (query: string): Promise<File[]> => {
              console.log("Loading suggestions for query:", query);

              try {
                // Fetch all suggestions
                const allSuggestions = await fetchFileSuggestions();
                console.log(
                  "Fetched suggestions count:",
                  allSuggestions.length,
                );

                // Filter by query
                const filtered = query
                  ? allSuggestions.filter((file) =>
                      file.path.toLowerCase().includes(query.toLowerCase()),
                    )
                  : allSuggestions;

                console.log("Filtered suggestions count:", filtered.length);
                return filtered;
              } catch (error) {
                console.error("Error fetching suggestions:", error);
                return [];
              }
            };

            // Handle selection of a suggestion
            const selectSuggestion = (
              filePath: string,
              range: { from: number; to: number },
            ): void => {
              console.log("Selected suggestion:", filePath);

              // Delete the @ and query
              view.dispatch(view.state.tr.delete(range.from, range.to));

              // Generate a unique ID for the tag
              const tagId = `file-${Date.now()}-${Math.random().toString(36).slice(2, 7)}`;

              // Create file tag node
              const fileTagAttrs = {
                filePath,
                id: tagId,
              };

              // Insert the file tag node
              view.dispatch(
                view.state.tr.insert(
                  range.from,
                  view.state.schema.nodes.fileTag.create(fileTagAttrs),
                ),
              );

              // Focus the editor again
              view.focus();

              // Generate formatted message for onChange
              let formattedMessage = "";
              const extractedTags: string[] = [];

              // Process each node to build the message with tags in correct positions
              view.state.doc.descendants((node) => {
                if (node.type.name === "text") {
                  formattedMessage += node.text;
                } else if (
                  node.type.name === "fileTag" &&
                  node.attrs.filePath
                ) {
                  const tagPath = node.attrs.filePath;
                  formattedMessage += ` @[${tagPath}] `;
                  extractedTags.push(tagPath);
                }
              });

              // Update parent component with the formatted message
              onChange(formattedMessage);
            };

            // Hide and destroy popup
            const destroyPopup = (): void => {
              if (popup) {
                popup.destroy();
                popup = null;
              }

              if (suggestionRoot) {
                suggestionRoot.unmount();
                suggestionRoot = null;
              }
            };

            return {
              update: async () => {
                const pluginState = FileSuggestionPluginKey.getState(
                  view.state,
                );

                // Skip if state is missing
                if (!pluginState) {
                  console.log("No state found for FileSuggestionPluginKey");
                  if (popup) destroyPopup();
                  return;
                }

                console.log(
                  "FileSuggestion update. Active:",
                  pluginState.active,
                  "Query:",
                  pluginState.query,
                );

                // Show popup if suggestions are active
                if (pluginState.active) {
                  // Get suggestions based on query
                  const suggestions = await loadSuggestions(pluginState.query);

                  // If we have suggestions, show the popup
                  if (suggestions && suggestions.length > 0) {
                    // Create popup if it doesn't exist
                    if (!popup) {
                      console.log("Creating suggestion popup");

                      // Find position for popup
                      const coords = view.coordsAtPos(pluginState.range.from);
                      console.log("Popup coordinates:", coords);

                      // Create container for React component
                      const element = document.createElement("div");
                      element.className = "suggestion-container";

                      // Create tippy instance with proper typing
                      popup = tippy(document.body, {
                        getReferenceClientRect: () => ({
                          x: coords.left,
                          y: coords.top,
                          width: 0,
                          height: 0,
                          top: coords.top,
                          bottom: coords.bottom,
                          left: coords.left,
                          right: coords.right,
                          toJSON: () => ({}),
                        }),
                        appendTo: () => document.body,
                        content: element,
                        showOnCreate: true,
                        interactive: true,
                        trigger: "manual",
                        placement: "bottom-start",
                        zIndex: 9999,
                      });

                      // Create React root
                      suggestionRoot = createRoot(element);
                    }

                    // Render React component
                    if (suggestionRoot) {
                      suggestionRoot.render(
                        <FileSuggestion
                          suggestions={suggestions}
                          query={pluginState.query}
                          onSelect={(filePath) => {
                            selectSuggestion(filePath, pluginState.range);
                            destroyPopup();
                          }}
                          onClose={() => destroyPopup()}
                        />,
                      );
                    }
                  } else {
                    // No suggestions, hide popup
                    if (popup) {
                      destroyPopup();
                    }
                  }
                } else if (popup) {
                  // Not active but popup exists, destroy it
                  destroyPopup();
                }
              },

              // Clean up
              destroy() {
                if (popup) {
                  popup.destroy();
                  popup = null;
                }

                if (suggestionRoot) {
                  suggestionRoot.unmount();
                  suggestionRoot = null;
                }
              },
            };
          },

          // Handle keyboard events
          props: {
            handleKeyDown(view, event) {
              const pluginState = FileSuggestionPluginKey.getState(view.state);

              // If no active suggestions, do nothing
              if (!pluginState?.active) {
                return false;
              }

              // Log for debugging
              console.log("Key pressed while suggestions active:", event.key);

              // Handle escape for closing suggestions
              if (event.key === "Escape") {
                // Hide suggestions by updating state
                view.dispatch(
                  view.state.tr.setMeta(FileSuggestionPluginKey, {
                    active: false,
                  }),
                );
                return true;
              }

              // Let Enter, ArrowUp, ArrowDown be handled by the React component
              if (["Enter", "ArrowUp", "ArrowDown"].includes(event.key)) {
                // Don't prevent default here, let the event propagate to the React component
                return false;
              }

              return false;
            },
          },
        }),
      ];
    },
  });

export default FileSuggestionExtension;
