# Project Euler in Lean4

Currently, problems 1-50 are solved.

- Mostly imperative style (`Id.run do ...`) is used.
- No proof. Partial functions and panicking functions are used.
- Performance is ignored, but every solution runs in less than one second (compiled executable).
- I didn't use any third-party library.

`lake pe exe` will run solutions for every problem.

## Discussion

- I don't know what is the proper way to measure the time of computation.
  - Is there a "black box" API (`α → IO α`) that inhibits the reordering of pure computations?
- I miss `Iterator` API of Rust.
  - I don't want to use `Range.toArray` if the array will be folded.
- The `elab` command is great for ad-hoc code generation.
- `!a[i]!` (array index + `not` operator) looks funny (because it is somewhat symmetric).
- `forIn` API missing:
  - Half-open ranges (hypothetical syntax: `[1:]`)
  - `Int` ranges
  - Reverse iteration.
