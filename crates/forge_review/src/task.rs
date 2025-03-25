//! Task Monad Implementation
//! 
//! This module provides a Task monad implementation for composing asynchronous operations
//! with error handling. The Task monad allows for:
//! 
//! - Sequencing operations with error short-circuiting
//! - Parallel execution of independent tasks
//! - Conditional execution based on runtime values
//! - Retry logic for failed operations
//! - Mapping and binding for composing complex workflows
//! 
//! # Examples
//! 
//! ```rust
//! use forge_review::task::{Task, TaskError, TaskErrorKind};
//! 
//! async fn example() -> forge_review::task::Result<String> {
//!     // Create a task using monadic style
//!     let task = Task::action(
//!         || async { Ok("step1_result".to_string()) },
//!         1,
//!         std::time::Duration::from_secs(0)
//!     )
//!     .bind(|step1_result| {
//!         // Use the result from step1 to create the next task
//!         Task::action(
//!             move || {
//!                 let data = step1_result.clone();
//!                 async move { 
//!                     println!("Using data from step1: {}", data);
//!                     Ok(data)
//!                 }
//!             },
//!             1,
//!             std::time::Duration::from_secs(0)
//!         )
//!     })
//!     .map(|step2_result| async move {
//!         // Transform the result
//!         Ok(format!("final_{}", step2_result))
//!     });
//!     
//!     // Execute the task
//!     task.execute().await
//! }
//! ```

use std::future::Future;
use std::time::Duration;
use std::fmt::Debug;
use std::sync::Arc;
use std::pin::Pin;
use std::error::Error as StdError;

/// Error type for tasks
#[derive(Debug, Clone)]
pub struct TaskError {
    /// The kind of error that occurred
    pub kind: TaskErrorKind,
    /// A detailed error message
    pub message: String,
}

/// Kinds of task errors
#[derive(Debug, Clone, PartialEq)]
pub enum TaskErrorKind {
    /// An action failed to execute successfully
    ActionFailed,
    /// A condition evaluation failed
    ConditionFailed,
    /// A sequence operation failed
    SequenceFailed,
    /// A parallel operation failed
    ParallelFailed,
    /// No else branch was provided for a false condition
    NoElseBranch,
    /// A for_each operation failed
    ForEachFailed,
    /// Retry attempts were exhausted
    RetryLimitExceeded,
    /// A map operation failed
    MapFailed,
    /// A bind operation failed
    BindFailed,
}

impl TaskError {
    /// Create a new task error
    pub fn new<S: Into<String>>(kind: TaskErrorKind, message: S) -> Self {
        Self {
            kind,
            message: message.into(),
        }
    }
}

impl std::fmt::Display for TaskError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}: {}", self.kind, self.message)
    }
}

impl StdError for TaskError {}

/// A result type for task operations
pub type Result<T> = std::result::Result<T, TaskError>;

/// A composable computation that can be executed in a monadic fashion.
/// 
/// The Task type represents a computation that can produce a value of type T
/// or fail with an error. Tasks can be composed using monadic operations
/// like map, bind, and chain.
///
/// # Type Parameters
///
/// * `T` - The type of value produced by the task
#[derive(Clone)]
pub enum Task<T>
where
    T: Clone + Send + Sync + 'static,
{
    /// A sequence of tasks to be executed in order
    Sequence(Vec<Task<T>>),
    
    /// A set of tasks to be executed in parallel
    Parallel(Vec<Task<T>>),
    
    /// An action that produces a value asynchronously
    Action {
        /// The function to execute
        func: Arc<dyn Fn() -> Pin<Box<dyn Future<Output = Result<T>> + Send>> + Send + Sync>,
        /// Maximum number of attempts for the action
        max_attempts: usize,
        /// Delay between retry attempts
        retry_delay: Duration,
    },
    
    /// A conditional task
    If {
        /// Function that evaluates the condition
        condition: Arc<dyn Fn() -> Pin<Box<dyn Future<Output = Result<bool>> + Send>> + Send + Sync>,
        /// Task to execute if the condition is true
        then_branch: Box<Task<T>>,
        /// Optional task to execute if the condition is false
        else_branch: Option<Box<Task<T>>>,
    },
    
    /// Execute a task for each item in a collection
    ForEach {
        /// Function that provides the items to iterate over
        items: Arc<dyn Fn() -> Pin<Box<dyn Future<Output = Result<Vec<T>>> + Send>> + Send + Sync>,
        /// Function that creates a task for each item
        task_creator: Arc<dyn Fn(T) -> Task<T> + Send + Sync>,
    },
    
    /// Transform the output of a task
    Map {
        /// The source task
        source: Box<Task<T>>,
        /// Function to transform the result
        transform: Arc<dyn Fn(T) -> Pin<Box<dyn Future<Output = Result<T>> + Send>> + Send + Sync>,
    },
    
    /// Chain tasks where each step depends on the previous one
    Bind {
        /// The source task
        source: Box<Task<T>>,
        /// Function to create the next task based on this task's result
        f: Arc<dyn Fn(T) -> Task<T> + Send + Sync>,
    },
    
    /// Pure value that produces a constant result
    Pure(T),
}

impl<T> Task<T>
where
    T: Clone + Send + Sync + 'static,
{
    /// Create a task that produces a constant value
    /// 
    /// This is the monadic "return" or "unit" function that wraps a value in the Task context.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use forge_review::task::Task;
    /// 
    /// let task = Task::pure(42);
    /// ```
    pub fn pure(value: T) -> Self {
        Task::Pure(value)
    }
    
    /// Create a sequence of tasks to be executed in order
    /// 
    /// Tasks will be executed in sequence, stopping if any task fails.
    /// The result of the sequence is the result of the last task.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use forge_review::task::Task;
    /// 
    /// let task1 = Task::pure(1);
    /// let task2 = Task::pure(2);
    /// let task3 = Task::pure(3);
    /// 
    /// let sequence = Task::sequence(vec![task1, task2, task3]);
    /// ```
    pub fn sequence(tasks: Vec<Task<T>>) -> Self {
        Task::Sequence(tasks)
    }
    
    /// Create a set of tasks to be executed in parallel
    /// 
    /// If the `futures` feature is enabled, tasks will be executed concurrently.
    /// Otherwise, they will be executed sequentially.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use forge_review::task::Task;
    /// 
    /// let task1 = Task::pure(1);
    /// let task2 = Task::pure(2);
    /// let task3 = Task::pure(3);
    /// 
    /// let parallel = Task::parallel(vec![task1, task2, task3]);
    /// ```
    pub fn parallel(tasks: Vec<Task<T>>) -> Self {
        Task::Parallel(tasks)
    }
    
    /// Create an action task
    /// 
    /// An action is the primary building block of the Task monad. It represents
    /// an asynchronous operation that may fail.
    /// 
    /// # Parameters
    /// 
    /// * `func` - The asynchronous function to execute
    /// * `max_attempts` - Maximum number of attempts to make (including the first try)
    /// * `retry_delay` - Delay between retry attempts
    /// 
    /// # Examples
    /// 
    /// ```
    /// use forge_review::task::{Task, TaskError, TaskErrorKind};
    /// use std::time::Duration;
    /// 
    /// let task = Task::action(
    ///     || async {
    ///         // Some async operation that might fail
    ///         Ok(42)
    ///     },
    ///     3, // Up to 3 attempts
    ///     Duration::from_millis(100)
    /// );
    /// ```
    pub fn action<F, Fut>(func: F, max_attempts: usize, retry_delay: Duration) -> Self
    where
        F: Fn() -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<T>> + Send + 'static,
    {
        Task::Action {
            func: Arc::new(move || Box::pin(func())),
            max_attempts,
            retry_delay,
        }
    }
    
    /// Create a simple action with no retries
    /// 
    /// This is a convenience method for creating an action that will not be retried.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use forge_review::task::Task;
    /// 
    /// let task = Task::simple_action(|| async {
    ///     // Some async operation that might fail
    ///     Ok(42)
    /// });
    /// ```
    pub fn simple_action<F, Fut>(func: F) -> Self
    where
        F: Fn() -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<T>> + Send + 'static,
    {
        Self::action(func, 1, Duration::from_millis(0))
    }
    
    /// Create a conditional task
    /// 
    /// Executes the `then_branch` if the condition evaluates to true,
    /// or the `else_branch` if it evaluates to false. If the condition is false
    /// and no `else_branch` is provided, the task will fail with a `NoElseBranch` error.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use forge_review::task::Task;
    /// 
    /// let conditional = Task::if_(
    ///     || async { Ok(true) },
    ///     Task::pure("then result"),
    ///     Some(Task::pure("else result"))
    /// );
    /// ```
    pub fn if_<F, Fut>(condition: F, then_branch: Task<T>, else_branch: Option<Task<T>>) -> Self
    where
        F: Fn() -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<bool>> + Send + 'static,
    {
        Task::If {
            condition: Arc::new(move || Box::pin(condition())),
            then_branch: Box::new(then_branch),
            else_branch: else_branch.map(Box::new),
        }
    }
    
    /// Create a task that executes for each item in a collection
    /// 
    /// For each item returned by the `items_provider`, creates and executes a task
    /// using the `task_creator` function. Returns the result of the last task executed.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use forge_review::task::Task;
    /// 
    /// let for_each = Task::for_each(
    ///     || async { Ok(vec![1, 2, 3]) },
    ///     |item| Task::pure(item * 2)
    /// );
    /// ```
    pub fn for_each<F, Fut, C>(items_provider: F, task_creator: C) -> Self
    where
        F: Fn() -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<Vec<T>>> + Send + 'static,
        C: Fn(T) -> Task<T> + Send + Sync + 'static,
    {
        Task::ForEach {
            items: Arc::new(move || Box::pin(items_provider())),
            task_creator: Arc::new(task_creator),
        }
    }
    
    /// Transform the output of a task
    /// 
    /// Applies a function to the result of the task. This is the functor `map` operation.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use forge_review::task::Task;
    /// 
    /// let task = Task::pure(21).map(|n| async move { Ok(n * 2) });
    /// ```
    pub fn map<F, Fut>(self, transform: F) -> Self
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<T>> + Send + 'static,
    {
        Task::Map {
            source: Box::new(self),
            transform: Arc::new(move |value| Box::pin(transform(value.clone()))),
        }
    }
    
    /// Chain tasks where each step depends on the previous one
    /// 
    /// This is the monadic `bind` or `flatMap` operation. It allows creating
    /// a new task based on the result of the current task.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use forge_review::task::Task;
    /// 
    /// let task = Task::pure(21).bind(|n| Task::pure(n * 2));
    /// ```
    pub fn bind<F>(self, f: F) -> Self
    where
        F: Fn(T) -> Task<T> + Send + Sync + 'static,
    {
        Task::Bind {
            source: Box::new(self),
            f: Arc::new(f),
        }
    }
    
    /// Chain a task after this one, keeping the result of this task
    /// 
    /// Executes this task, then the next task, but keeps the result of this task.
    /// This is similar to the `then` operator in some monadic libraries.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use forge_review::task::Task;
    /// 
    /// let task = Task::pure(21).chain(Task::pure(42));
    /// // After execution, the result will be 21, not 42
    /// ```
    pub fn chain(self, next: Task<T>) -> Self {
        let next_box = Box::new(next);
        self.bind(move |value| {
            let value_clone = value.clone();
            let next_clone = (*next_box).clone();
            Task::Map {
                source: Box::new(next_clone),
                transform: Arc::new(move |_| {
                    let val = value_clone.clone();
                    Box::pin(async move { Ok(val) })
                }),
            }
        })
    }
    
    /// Add retry capabilities to an existing task
    /// 
    /// Wraps this task with retry logic, allowing it to be retried multiple times
    /// if it fails.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use forge_review::task::Task;
    /// use std::time::Duration;
    /// 
    /// let task = Task::simple_action(|| async { Ok(42) })
    ///     .with_retry(3, Duration::from_millis(100));
    /// ```
    pub fn with_retry(self, max_attempts: usize, retry_delay: Duration) -> Self {
        let self_clone = self.clone();
        Task::Action {
            func: Arc::new(move || {
                let task = self_clone.clone();
                Box::pin(async move {
                    task.execute().await
                })
            }),
            max_attempts,
            retry_delay,
        }
    }
    
    /// Execute the task
    /// 
    /// This method runs the task and returns the result.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use forge_review::task::Task;
    /// 
    /// async fn run_example() {
    ///     let task = Task::pure(42);
    ///     let result = task.execute().await;
    ///     assert_eq!(result.unwrap(), 42);
    /// }
    /// ```
    pub async fn execute(self) -> Result<T> {
        Box::pin(self.execute_inner()).await
    }

    async fn execute_inner(self) -> Result<T> {
        match self {
            Task::Pure(value) => {
                Ok(value)
            }
            
            Task::Sequence(tasks) => {
                let mut last_result = None;
                
                for task in tasks {
                    match task.execute().await {
                        Ok(result) => last_result = Some(result),
                        Err(e) => return Err(e),
                    }
                }
                
                match last_result {
                    Some(result) => Ok(result),
                    None => Err(TaskError::new(
                        TaskErrorKind::SequenceFailed, 
                        "Sequence contained no tasks"
                    )),
                }
            }
            
            Task::Parallel(tasks) => {
                if tasks.is_empty() {
                    return Err(TaskError::new(
                        TaskErrorKind::ParallelFailed,
                        "Parallel task list was empty"
                    ));
                }
                
                // Use futures if available
                #[cfg(feature = "futures")]
                {
                    use futures::future::join_all;
                    let futures = tasks.into_iter()
                        .map(|task| task.execute())
                        .collect::<Vec<_>>();
                    
                    let results = join_all(futures).await;
                    
                    // Find first error, or return the last successful result
                    let mut last_result = None;
                    
                    for result in results {
                        match result {
                            Ok(value) => last_result = Some(value),
                            Err(e) => return Err(e),
                        }
                    }
                    
                    last_result.ok_or_else(|| TaskError::new(
                        TaskErrorKind::ParallelFailed,
                        "No successful results from parallel tasks"
                    ))
                }
                
                // Fallback implementation
                #[cfg(not(feature = "futures"))]
                {
                    let mut last_result = None;
                    for task in tasks {
                        match task.execute().await {
                            Ok(result) => last_result = Some(result),
                            Err(e) => return Err(e),
                        }
                    }
                    
                    last_result.ok_or_else(|| TaskError::new(
                        TaskErrorKind::ParallelFailed,
                        "No successful results from parallel tasks"
                    ))
                }
            }
            
            Task::Action { func, max_attempts, retry_delay } => {
                let mut attempts = 0;
                let mut last_error = None;
                
                while attempts < max_attempts {
                    attempts += 1;
                    
                    match func().await {
                        Ok(result) => return Ok(result),
                        Err(e) => {
                            last_error = Some(e);
                            
                            if attempts < max_attempts {
                                // Sleep with tokio if available, otherwise use std
                                #[cfg(feature = "time")]
                                tokio::time::sleep(retry_delay).await;
                                
                                #[cfg(not(feature = "time"))]
                                {
                                    let duration_millis = retry_delay.as_millis() as u64;
                                    if duration_millis > 0 {
                                        std::thread::sleep(std::time::Duration::from_millis(duration_millis));
                                    }
                                }
                            }
                        }
                    }
                }
                
                Err(last_error.unwrap_or_else(|| TaskError::new(
                    TaskErrorKind::ActionFailed,
                    format!("Action failed after {} attempts", max_attempts)
                )))
            }
            
            Task::If { condition, then_branch, else_branch } => {
                match condition().await {
                    Ok(true) => then_branch.execute().await,
                    Ok(false) => {
                        match else_branch {
                            Some(branch) => branch.execute().await,
                            None => Err(TaskError::new(
                                TaskErrorKind::NoElseBranch,
                                "Condition was false but no else branch was provided"
                            )),
                        }
                    }
                    Err(e) => Err(e),
                }
            }
            
            Task::ForEach { items, task_creator } => {
                match items().await {
                    Ok(items) => {
                        if items.is_empty() {
                            return Err(TaskError::new(
                                TaskErrorKind::ForEachFailed,
                                "ForEach had no items to process"
                            ));
                        }
                        
                        let mut last_result = None;
                        
                        for item in items {
                            let task = task_creator(item);
                            match task.execute().await {
                                Ok(result) => last_result = Some(result),
                                Err(e) => return Err(e),
                            }
                        }
                        
                        last_result.ok_or_else(|| TaskError::new(
                            TaskErrorKind::ForEachFailed,
                            "ForEach returned no results"
                        ))
                    }
                    Err(e) => Err(e),
                }
            }
            
            Task::Map { source, transform } => {
                match source.execute().await {
                    Ok(value) => transform(value).await,
                    Err(e) => Err(e),
                }
            }
            
            Task::Bind { source, f } => {
                match source.execute().await {
                    Ok(value) => {
                        let next_task = f(value);
                        next_task.execute().await
                    }
                    Err(e) => Err(e),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Mutex};
    
    async fn run_test<T: Clone + Send + Sync + 'static>(task: Task<T>) -> Result<T> {
        task.execute().await
    }

    #[test]
    fn test_pure() {
        let task = Task::pure(42);
        
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            run_test(task).await
        });
        
        assert_eq!(result.unwrap(), 42);
    }
    
    #[test]
    fn test_sequence() {
        let counter = Arc::new(Mutex::new(0));
        
        let c1 = counter.clone();
        let task1 = Task::action(
            move || {
                let c = c1.clone();
                async move {
                    let mut count = c.lock().unwrap();
                    *count += 1;
                    Ok(*count)
                }
            },
            1,
            Duration::from_millis(1)
        );
        
        let c2 = counter.clone();
        let task2 = Task::action(
            move || {
                let c = c2.clone();
                async move {
                    let mut count = c.lock().unwrap();
                    *count += 2;
                    Ok(*count)
                }
            },
            1,
            Duration::from_millis(1)
        );
        
        let c3 = counter.clone();
        let task3 = Task::action(
            move || {
                let c = c3.clone();
                async move {
                    let mut count = c.lock().unwrap();
                    *count += 3;
                    Ok(*count)
                }
            },
            1,
            Duration::from_millis(1)
        );
        
        let sequence_task = Task::sequence(vec![task1, task2, task3]);
        
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            run_test(sequence_task).await
        });
        
        // The final result should be 6 (1+2+3) and each task should run in sequence
        assert_eq!(result.unwrap(), 6);
        assert_eq!(*counter.lock().unwrap(), 6);
    }
    
    #[test]
    fn test_map() {
        let task = Task::pure(42)
            .map(|n| async move { Ok(n * 2) });
            
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            run_test(task).await
        });
        
        assert_eq!(result.unwrap(), 84);
    }
    
    #[test]
    fn test_bind() {
        let task = Task::pure(42)
            .bind(|n| Task::pure(n * 2));
            
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            run_test(task).await
        });
        
        assert_eq!(result.unwrap(), 84);
    }
    
    #[test]
    fn test_chain() {
        let first = Task::pure(42);
        let second = Task::pure(84);
        
        let chained = first.chain(second);
        
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            run_test(chained).await
        });
        
        // Should keep the result of the first task
        assert_eq!(result.unwrap(), 42);
    }
    
    #[test]
    fn test_conditionals() {
        // Test true condition
        let true_task = Task::if_(
            || async { Ok(true) },
            Task::pure("then_branch"),
            Some(Task::pure("else_branch"))
        );
        
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            run_test(true_task).await
        });
        
        assert_eq!(result.unwrap(), "then_branch");
        
        // Test false condition
        let false_task = Task::if_(
            || async { Ok(false) },
            Task::pure("then_branch"),
            Some(Task::pure("else_branch"))
        );
        
        let result = rt.block_on(async {
            run_test(false_task).await
        });
        
        assert_eq!(result.unwrap(), "else_branch");
        
        // Test false condition with no else branch
        let false_no_else = Task::if_(
            || async { Ok(false) },
            Task::pure("then_branch"),
            None
        );
        
        let result = rt.block_on(async {
            run_test(false_no_else).await
        });
        
        assert!(result.is_err());
        if let Err(e) = result {
            assert!(matches!(e.kind, TaskErrorKind::NoElseBranch));
        }
    }
    
    #[test]
    fn test_retry_success_after_failure() {
        let attempt_counter = Arc::new(Mutex::new(0));
        
        let counter = attempt_counter.clone();
        let retry_task: Task<i32> = Task::action(
            move || {
                let c = counter.clone();
                async move {
                    let mut count = c.lock().unwrap();
                    *count += 1;
                    
                    // Fail on first attempt, succeed on second
                    if *count < 2 {
                        Err(TaskError::new(TaskErrorKind::ActionFailed, "Not ready yet"))
                    } else {
                        Ok(*count)
                    }
                }
            },
            2, // Allow up to 2 attempts (first try + 1 retry)
            Duration::from_millis(10)
        );
        
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            run_test(retry_task).await
        });
        
        assert_eq!(result.unwrap(), 2); // Second attempt succeeded
        assert_eq!(*attempt_counter.lock().unwrap(), 2); // Two attempts were made
    }
    
    #[test]
    fn test_retry_all_failures() {
        let attempt_counter = Arc::new(Mutex::new(0));
        
        let counter = attempt_counter.clone();
        let retry_task: Task<i32> = Task::action(
            move || {
                let c = counter.clone();
                async move {
                    let mut count = c.lock().unwrap();
                    *count += 1;
                    
                    // Always fail
                    Err(TaskError::new(TaskErrorKind::ActionFailed, "Never succeeds"))
                }
            },
            2, // Allow up to 2 attempts (first try + 1 retry)
            Duration::from_millis(10)
        );
        
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            run_test(retry_task).await
        });
        
        assert!(result.is_err());
        assert_eq!(*attempt_counter.lock().unwrap(), 2);
    }
    
    #[test]
    fn test_for_each() {
        let counter = Arc::new(Mutex::new(0));
        
        let c = counter.clone();
        let for_each_task: Task<String> = Task::for_each(
            || async { Ok(vec!["a".to_string(), "b".to_string(), "c".to_string()]) },
            move |item: String| {
                let c = c.clone();
                Task::action(
                    move || {
                        let c = c.clone();
                        let item = item.clone();
                        async move {
                            let mut count = c.lock().unwrap();
                            *count += 1;
                            println!("Processing item: {}", item);
                            Ok(item)  // Return the string, not the count
                        }
                    },
                    1,
                    Duration::from_millis(1)
                )
            }
        );
        
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            run_test(for_each_task).await
        });
        
        assert_eq!(result.unwrap(), "c"); // Last item processed
        assert_eq!(*counter.lock().unwrap(), 3); // Three increments total
    }
    
    #[test]
    fn test_with_retry() {
        let attempt_counter = Arc::new(Mutex::new(0));
        
        let counter = attempt_counter.clone();
        let inner_task: Task<i32> = Task::action(
            move || {
                let c = counter.clone();
                async move {
                    let mut count = c.lock().unwrap();
                    *count += 1;
                    
                    // Always fail
                    Err(TaskError::new(TaskErrorKind::ActionFailed, "Never succeeds"))
                }
            },
            1, // No retries at this level (just 1 attempt)
            Duration::from_millis(10)
        );
        
        // Add retries to the existing task (2 attempts total)
        let with_retry_task = inner_task.with_retry(2, Duration::from_millis(10));
        
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            run_test(with_retry_task).await
        });
        
        assert!(result.is_err());
        assert_eq!(*attempt_counter.lock().unwrap(), 2);
    }
    
    #[test]
    fn test_simple_action() {
        // Test the simple_action constructor which creates an action with no retries
        let task = Task::simple_action(|| async {
            Ok(42)
        });
        
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            run_test(task).await
        });
        
        assert_eq!(result.unwrap(), 42);
    }
    
    #[test]
    fn test_monadic_composition() {
        // This test verifies a more complex composition of tasks
        let task: Task<String> = Task::action(
            || async { Ok("step1_result".to_string()) },
            1,
            Duration::from_secs(0)
        )
        .bind(|step1_result| {
            // Use the result from step1 to create the next task
            Task::action(
                move || {
                    let data = step1_result.clone();
                    async move { 
                        Ok(data)
                    }
                },
                1,
                Duration::from_secs(0)
            )
        })
        .map(|step2_result| async move {
            // Transform the result
            Ok(format!("final_{}", step2_result))
        });
        
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            run_test(task).await
        });
        
        assert_eq!(result.unwrap(), "final_step1_result");
    }
    
    #[test]
    fn test_custom_error_handling() {
        // A test to show we can map TaskError to more specialized errors
        let task = Task::action(
            || async { 
                Err(TaskError::new(TaskErrorKind::ActionFailed, "Something went wrong"))
            },
            1,
            Duration::from_millis(0)
        )
        .map(|_| async {
            // This won't execute since the action fails
            Ok("This won't be returned".to_string()) 
        });
        
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
            
        let result = rt.block_on(async {
            task.execute().await
        });
        
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.kind, TaskErrorKind::ActionFailed);
        assert_eq!(err.message, "Something went wrong");
    }
} 