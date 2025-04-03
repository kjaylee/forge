# Context Compaction Strategy Trait System

## Objective

Refactor the existing context compaction system in Forge to use a trait-based approach with multiple strategy implementations. This will improve extensibility, maintainability, and efficiency of the compaction system while providing robust implementations for both summarization and sliding window compaction approaches.

## Current Implementation Analysis

The existing compaction system in `compaction.rs` has several components:

1. A `ContextCompactor<Services>` struct that manages compaction operations
2. Methods for identifying and compressing sequences of messages through summarization
3. A `find_sequence` function to identify compressible message ranges
4. Comprehensive tests for various scenarios and edge cases

The current flow:
- `compact_context` checks if compaction is needed based on thresholds
- If needed, it tries to find a compressible sequence with `find_sequence`
- If a sequence is found, it's summarized and replaced with a summary message
- If no sequence is found, the context is returned unchanged (no fallback)

## Proposed Trait-Based System

### 1. Core Components

1. **CompactionStrategy Trait**: Defines the interface for all compaction strategies
2. **Strategy Implementations**:
   - `SummarizationStrategy`: Refactored from existing implementation
   - `SlidingWindowStrategy`: New implementation for the sliding window approach
3. **Enhanced ContextCompactor**: Supports multiple strategies with automatic selection and fallback
4. **CompactionServices Interface**: Provides access to required services for strategies

### 2. File Structure

```
forge_domain/src/
├── compaction/
│   ├── mod.rs               # Module exports and core ContextCompactor
│   ├── strategy.rs          # CompactionStrategy trait and CompactionServices
│   ├── summarization.rs     # SummarizationStrategy implementation
│   ├── sliding_window.rs    # SlidingWindowStrategy implementation
│   └── utils.rs             # Shared utility functions
└── compaction.rs            # Legacy file (to be deprecated)
```

### 3. Core Trait and Interface Design

```rust
/// Provides access to services needed by compaction strategies
#[async_trait]
pub trait CompactionServices: Send + Sync {
    fn template_service(&self) -> &dyn TemplateService;
    fn provider_service(&self) -> &dyn ProviderService;
}

/// Defines a strategy for compacting conversation contexts
#[async_trait]
pub trait CompactionStrategy: Send + Sync {
    /// Unique identifier for this strategy
    fn id(&self) -> &'static str;
    
    /// Description of what this strategy does
    fn description(&self) -> &'static str;
    
    /// Determines if this strategy can be applied to the given context
    fn is_applicable(&self, compact: &Compact, context: &Context) -> bool;
    
    /// Applies the compaction strategy to a context
    /// Returns the compacted context and a measurement of impact (e.g. reduction in tokens/messages)
    async fn compact(&self, 
                    compact: &Compact, 
                    context: Context, 
                    services: &dyn CompactionServices) -> Result<(Context, CompactionImpact)>;
}

/// Measures the impact of a compaction operation
struct CompactionImpact {
    /// Original number of messages
    original_messages: usize,
    /// New number of messages after compaction
    new_messages: usize,
    /// Estimated reduction in token count
    token_reduction: Option<u64>,
}

impl CompactionImpact {
    /// Determines if this compaction had significant impact
    /// A compaction is significant if it reduced the context size by at least 20%
    fn is_significant(&self) -> bool {
        if self.original_messages == 0 {
            return false;
        }
        
        let reduction_percentage = 100.0 * (self.original_messages - self.new_messages) as f32 / self.original_messages as f32;
        reduction_percentage >= 20.0
    }
}
```

### 4. Enhanced ContextCompactor

```rust
#[derive(Clone)]
pub struct ContextCompactor<S> {
    services: Arc<S>,
    strategies: Vec<Box<dyn CompactionStrategy>>,
}

impl<S: Services> ContextCompactor<S> {
    // Create with default strategies
    pub fn new(services: Arc<S>) -> Self {
        let mut compactor = Self {
            services,
            strategies: Vec::new(),
        };
        
        // Register default strategies in order of preference
        compactor.register_strategy(Box::new(SummarizationStrategy));
        compactor.register_strategy(Box::new(SlidingWindowStrategy));
        
        compactor
    }
    
    // Register a custom strategy
    pub fn register_strategy(&mut self, strategy: Box<dyn CompactionStrategy>) {
        self.strategies.push(strategy);
    }
    
    // Main compaction method
    pub async fn compact_context(&self, agent: &Agent, context: Context) -> Result<Context> {
        if let Some(ref compact) = agent.compact {
            if !compact.should_compact(&context) {
                return Ok(context);
            }

            debug!(agent_id = %agent.id, "Context compaction triggered");
            
            // Try each strategy in order until one is applicable and provides significant impact
            let mut current_context = context;
            
            for strategy in &self.strategies {
                if strategy.is_applicable(compact, &current_context) {
                    debug!(
                        agent_id = %agent.id,
                        strategy = strategy.id(),
                        "Attempting compaction strategy"
                    );
                    
                    let (compacted, impact) = strategy.compact(
                        compact, 
                        current_context.clone(), 
                        self.services.as_ref()
                    ).await?;
                    
                    // If this strategy had significant impact, use its result
                    if impact.is_significant() {
                        info!(
                            agent_id = %agent.id,
                            strategy = strategy.id(),
                            original_messages = impact.original_messages,
                            new_messages = impact.new_messages,
                            "Compaction strategy had significant impact"
                        );
                        return Ok(compacted);
                    }
                    
                    // Otherwise, continue with the next strategy using the original context
                    debug!(
                        agent_id = %agent.id,
                        strategy = strategy.id(),
                        "Compaction strategy had insufficient impact, trying next strategy"
                    );
                }
            }
            
            // If no strategy had significant impact, return the original context
            debug!(agent_id = %agent.id, "No compaction strategy had significant impact");
        }
        
        Ok(context)
    }
}
```

### 5. Strategy Implementations

#### Summarization Strategy

```rust
pub struct SummarizationStrategy;

#[async_trait]
impl CompactionStrategy for SummarizationStrategy {
    fn id(&self) -> &'static str {
        "summarization"
    }
    
    fn description(&self) -> &'static str {
        "Compacts by summarizing message sequences"
    }
    
    fn is_applicable(&self, compact: &Compact, context: &Context) -> bool {
        find_sequence(context, compact.retention_window).is_some()
    }
    
    async fn compact(&self, compact: &Compact, context: Context, services: &dyn CompactionServices) 
        -> Result<(Context, CompactionImpact)> 
    {
        // Record original message count
        let original_messages = context.messages.len();
        
        // Find and summarize a sequence
        let compacted_context = self.summarize_sequence(compact, context, services).await?;
        
        // Create impact measurement
        let impact = CompactionImpact {
            original_messages,
            new_messages: compacted_context.messages.len(),
            token_reduction: Some(estimate_token_reduction(&context, &compacted_context)),
        };
        
        Ok((compacted_context, impact))
    }
}
```

#### Sliding Window Strategy

```rust
pub struct SlidingWindowStrategy;

#[async_trait]
impl CompactionStrategy for SlidingWindowStrategy {
    fn id(&self) -> &'static str {
        "sliding_window"
    }
    
    fn description(&self) -> &'static str {
        "Compacts by dropping oldest messages"
    }
    
    fn is_applicable(&self, _compact: &Compact, _context: &Context) -> bool {
        // Always applicable as a fallback
        true
    }
    
    async fn compact(&self, compact: &Compact, context: Context, _services: &dyn CompactionServices) 
        -> Result<(Context, CompactionImpact)> 
    {
        // Record original message count
        let original_messages = context.messages.len();
        
        // Implement sliding window logic
        let compacted_context = self.drop_oldest_messages(compact, context)?;
        
        // Create impact measurement
        let impact = CompactionImpact {
            original_messages,
            new_messages: compacted_context.messages.len(),
            token_reduction: Some(estimate_token_reduction(&context, &compacted_context)),
        };
        
        Ok((compacted_context, impact))
    }
}
```

## Implementation Plan

### 1. Create the Basic Structure

1. Create the `compaction` directory and its files
2. Define the `CompactionStrategy` and `CompactionServices` traits
3. Move utility functions like `find_sequence` to `utils.rs`

### 2. Implement the Summarization Strategy

1. Extract the existing summarization logic to `SummarizationStrategy`
2. Adapt it to work with the new traits and interfaces
3. Add impact measurement to the implementation
4. Write tests for the strategy in isolation

### 3. Implement the Sliding Window Strategy

1. Implement the `SlidingWindowStrategy` based on our previous plan
2. Add utility functions for finding drop boundaries and handling tool chains
3. Add impact measurement to the implementation 
4. Write tests for the sliding window implementation

### 4. Implement the Enhanced ContextCompactor

1. Create the new `ContextCompactor` with strategy registration
2. Implement the strategy execution pipeline with impact evaluation
3. Add automatic fallback to alternative strategies if impact is insufficient
4. Write tests for strategy selection and fallback behavior

### 5. Update Configuration and Integration

1. Create a smooth transition path for existing code
2. Update documentation to explain the new compaction system

### 6. Migrate Existing Code

1. Add deprecation notices to the old implementation
2. Update usage sites to use the new API
3. Eventually remove the old implementation in a future release

## Testing Strategy

1. **Unit tests for each strategy**:
   - Test different context patterns and edge cases
   - Test strategy-specific behavior
   - Test impact measurements

2. **Integration tests for the compactor**:
   - Test the strategy selection mechanism
   - Test the impact-based fallback behavior  
   - Test the complete compaction flow with multiple strategies
   - Test with real-world context examples

3. **Performance tests**:
   - Compare performance before and after refactoring
   - Identify any potential bottlenecks

## Verification Criteria

The implementation will be considered successful if:

1. All existing tests continue to pass
2. New tests for the strategy implementations pass
3. Both summarization and sliding window compaction work as expected
4. The system automatically selects the appropriate strategy based on context
5. Strategies that don't have significant impact are automatically skipped in favor of better alternatives
6. Backward compatibility is maintained for existing code

## Benefits

The refactored design offers several key benefits:

1. **Extensibility**: New strategies can be implemented without modifying core code
2. **Automatic Optimization**: The system automatically selects the most effective strategy
3. **Maintainability**: Clear separation of concerns makes the code more maintainable
4. **Testability**: Each component can be tested in isolation
5. **Robustness**: Better fallback behavior when the primary strategy isn't effective
6. **Implementation Detail**: Strategy selection is hidden from users/agents; they just get the best results

## Future Enhancements

Once the trait-based system is in place, future improvements could include:

1. **Additional strategies**: Implement more sophisticated compaction approaches
2. **Adaptive strategy selection**: Improve the algorithm for selecting the best strategy based on context content
3. **Strategy metrics**: Track and report on the effectiveness of different strategies
4. **Parallel strategy execution**: Try multiple strategies in parallel and choose the best result

This refactoring lays the groundwork for a more efficient, maintainable, and powerful compaction system in Forge.