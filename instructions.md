Project Objective:

- Our main objective is building a coding agent called - "forge".
- We will follow clean architecture with - separate crate for each layer having forge_domain at its core.
- When we say ADT we mean Algebraic Data Types which includes Sum and Product types.
- Every thing needs to revolve around our core domain which is the "Agent"

Before Creating a Plan:

- Do a `git diff` to see what has changed so far.
- Compile the code using `cargo check --workspace`.
- Read all the files and mentions URLs

In the Plan:

- Contains information about the components (functions, types, modules etc.) that will modified or added.
- Optimize the plan at least 2 times before yield to the user for approval.
- Ensure there is a verification step that includes running the tests.

Verification Step:

- Run all the tests using `cargo test --workspace`
- Review original objective and compare the changes that were performed.

Tips to be Successful:

- Run snapshot test using the `cargo insta test --accept` or the command will never complete.

Code Guidelines:

1. Write unit tests as follows:
   a. Ensure there is minimum boilerplate code and leverage helper functions.
   b. Define three variables: `setup`, `actual` and `expected`.
   c. Use `pretty_assertions` always.

   ```rust
   let setup = ...;
   let actual = ... ;
   let expected = ... ;
   assert_eq!(actual, expected);
   ```
