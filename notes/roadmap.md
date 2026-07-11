# Roadmap

Formalization targets and their status. One entry per target.

Status values: `idea` → `stated` (definition/statement written, may contain `sorry`) → `proved` (compiles, no `sorry`).

## Targets

- **Linked Cluster Theorem (finite temperature)** — status: `idea`.
  Goal: formalize the statement that `log Z` (thermal/Matsubara perturbation theory, `Z = tr e^{-βH}`) admits a cumulant expansion containing only connected-diagram contributions, on a countably infinite-dimensional lattice model. Proof strategy: derive from a general moment-cumulant combinatorial theorem (partition lattice / Möbius function), specialized to thermal expectation values. See `notes/model-and-assumptions.md` for the full setup and the scope note on convergence/trace-class questions (deliberately excluded from this target — the combinatorial core is treated as a formal/algebraic identity).
  Prerequisite building blocks likely needed before the main proof: (1) partition-lattice Möbius/moment-cumulant formula in Mathlib-compatible form, (2) definition of thermal expectation values and their cumulants, (3) a notion of "connected" for set partitions / diagrams matching the physics definition.

- **Basic quantum field theory formalization** — status: `idea`.
  Prerequisite groundwork target: the minimal scaffolding needed before stating either theorem above — e.g. creation/annihilation operator algebra (CCR/CAR), Fock space construction, and normal ordering, on the countably infinite-dimensional lattice setting chosen for this project. Precise scope to be filled in `notes/model-and-assumptions.md`.

- **Finite-temperature Bloch–de Dominicis theorem** — status: `idea`.
  Goal: formalize the thermal-average analogue of Wick's theorem — that a thermal expectation value of a product of creation/annihilation operators decomposes into a sum over all full pairings (contractions), each a product of two-operator thermal averages. Depends on the QFT groundwork target above. Relationship to the Linked Cluster Theorem target to be clarified in `notes/model-and-assumptions.md` (likely used as an input to it, since Wick-type pairing underlies the diagrammatic expansion).

## Completed

(To be filled)
