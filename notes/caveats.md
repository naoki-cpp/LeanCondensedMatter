# Caveats

Known pitfalls, past mistakes, and things to watch out for. Add an entry whenever an error costs time so it is not repeated.

## Formalization pitfalls

- **No trace-class/Schatten-class theory in Mathlib (as of the Mathlib revision pinned in `lakefile.toml`).** `LinearMap.trace` requires finite-dimensionality. This blocks a direct extension of `QuantumTheory.DensityOperator` (`LeanCondensedMatter/QuantumTheory/DensityOperator.lean`) to the countably-infinite-dimensional lattice setting chosen in `notes/model-and-assumptions.md` for the Linked Cluster Theorem target — `Z = tr e^{-βH}` needs a trace on an infinite-dimensional space. Until such machinery exists (in Mathlib or built here), density-operator work stays scoped to finite-dimensional `H`.

## Physics pitfalls

(To be filled)
