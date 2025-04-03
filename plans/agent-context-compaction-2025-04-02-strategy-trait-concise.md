# Context Compaction Strategy Trait System - Concise Plan

## Objective

Refactor Forge's context compaction system to use a trait-based approach with multiple strategy implementations. The system will automatically select the most effective compaction strategy as an implementation detail, improving robustness and maintainability.

## Key Components

1. **CompactionStrategy Trait**: Core interface for all compaction strategies
2. **Impact Measurement**: System to evaluate strategy effectiveness
3. **Strategy Implementations**:
   - `SummarizationStrategy`: Current approach of finding and summarizing message sequences
   - `SlidingWindowStrategy`: New approach of dropping oldest messages when needed
4. **Enhanced ContextCompactor**: Tries strategies in order and selects the one with significant impact

## Core Trait Design

```rust
#[async_trait]
pub trait CompactionStrategy: Send + Sync {
    fn id(&self) -> &'static str;
    fn description(&self) -> &'static str;
    fn is_applicable(&self, compact: &Compact, context: &Context) -> bool;
    
    async fn compact(
        &self, 
        compact: &Compact, 
        context: Context, 
        services: &dyn CompactionServices
    ) -> Result<(Context, CompactionImpact)>;
}
```

## Impact Measurement

```rust
struct CompactionImpact {
    original_messages: usize,
    new_messages: usize,
    token_reduction: Option<u64>,
    
    fn is_significant(&self) -> bool {
        // Returns true if at least 20% reduction was achieved
    }
}
```

## File Structure

```
forge_domain/src/
├── compaction/
│   ├── mod.rs               # Core ContextCompactor
│   ├── strategy.rs          # Core traits
│   ├── summarization.rs     # Summarization strategy
│   ├── sliding_window.rs    # Sliding window strategy
│   └── utils.rs             # Shared utility functions
└── compaction.rs            # Legacy file (to be deprecated)
```

## Implementation Steps

1. **Create Basic Structure**:
   - Define traits and interfaces
   - Move utility functions to shared location

2. **Implement Summarization Strategy**:
   - Refactor existing logic into strategy implementation
   - Add impact measurement

3. **Implement Sliding Window Strategy**:
   - Create implementation based on previous plan
   - Add impact measurement and utility functions

4. **Enhance ContextCompactor**:
   - Add strategy registration and ordering
   - Implement impact-based selection
   - Try alternative strategies when impact is insufficient

5. **Migrate Existing Code**:
   - Add compatibility layer
   - Update documentation
   - Deprecate old implementation

## Benefits

1. **Extensibility**: Easily add new strategies by implementing the trait
2. **Automatic Selection**: System tries strategies in order of preference
3. **Effectiveness**: Strategies with insufficient impact are skipped
4. **Maintainability**: Clear separation of concerns
5. **Implementation Detail**: Strategy selection is hidden from users; they just get the best results
6. **Robustness**: Better fallback behavior with multiple strategies

This design hides compaction strategy details from users/agents while internally providing a robust, extensible system that automatically selects the most effective approach.