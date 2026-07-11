# Roadmap

Formalization targets and their status. One entry per target.

Status values: `idea` → `stated` (definition/statement written, may contain `sorry`) → `proved` (compiles, no `sorry`).

## Approach

The Linked Cluster Theorem target rests on two largely independent prerequisite tracks that both feed into it. Work on the two tracks can proceed in parallel; the top-level theorem waits on both.

```
Track A: quantum theory foundations       Track B: combinatorics
  Basic QFT formalization                   Partition-lattice Möbius /
    -> Bloch-de Dominicis theorem              moment-cumulant formula
              \                                      /
               \                                    /
                -> Linked Cluster Theorem (finite temperature)
```

## Targets

### Track A — quantum theory foundations

- **Minimal axiomatic quantum theory foundation** — status: `stated`.
  State-space postulate and observable definition (`QuantumTheory.State`, `QuantumTheory.Observable`) and the expectation value they define, with reality of expectation values proved (`expValue_im_eq_zero`) and phase indeterminacy proved (`expValue_smul_of_norm_eq_one`). See `LeanCondensedMatter/QuantumTheory/Postulates.lean` and `notes/model-and-assumptions.md`. Entry point beneath the QFT groundwork target below.

- **Density operators and the Born rule (finite-dimensional)** — status: `stated`.
  Density-operator postulate (`QuantumTheory.DensityOperator`, positive trace-1 operator) and general (POVM) measurement postulate (`QuantumTheory.POVM`, `QuantumTheory.prob`), with the Born rule's probabilities proved to sum to `1` (`sum_prob_eq_one`). Purification (`QuantumTheory.pure`) and purity (`QuantumTheory.purity`) defined, with `purity_pure : purity (pure ψ) = 1` proved. See `LeanCondensedMatter/QuantumTheory/DensityOperator.lean`. **Scoped to finite-dimensional `H`** — see the trace-class caveat in `notes/caveats.md`; extending to the countably-infinite lattice setting used elsewhere in this roadmap needs that gap closed first.

- **Basic quantum field theory formalization** — status: `idea`.
  Prerequisite groundwork target: the minimal scaffolding needed before stating either theorem below — e.g. creation/annihilation operator algebra (CCR/CAR), Fock space construction, and normal ordering, on the countably infinite-dimensional lattice setting chosen for this project. Precise scope to be filled in `notes/model-and-assumptions.md`.

- **Finite-temperature Bloch–de Dominicis theorem** — status: `idea`.
  Goal: formalize the thermal-average analogue of Wick's theorem — that a thermal expectation value of a product of creation/annihilation operators decomposes into a sum over all full pairings (contractions), each a product of two-operator thermal averages. Depends on the QFT groundwork target above.

### Track B — combinatorics

- **Partition-lattice Möbius / moment-cumulant formula** — status: `idea`.
  Goal: formalize the general combinatorial moment-cumulant theorem on the lattice of set partitions (Möbius function of the partition lattice), in a form specializable to thermal expectation values. Independent of Track A — pure combinatorics, no physics content.

### Combined

- **Linked Cluster Theorem (finite temperature)** — status: `idea`.
  Goal: formalize the statement that `log Z` (thermal/Matsubara perturbation theory, `Z = tr e^{-βH}`) admits a cumulant expansion containing only connected-diagram contributions, on a countably infinite-dimensional lattice model. Depends on both tracks above: the Bloch–de Dominicis theorem (Track A) supplies the pairing structure, the moment-cumulant formula (Track B) supplies the connectedness argument. See `notes/model-and-assumptions.md` for the full setup and the scope note on convergence/trace-class questions (deliberately excluded — the combinatorial core is treated as a formal/algebraic identity).
  Remaining building block once both tracks land: (1) definition of thermal expectation values and their cumulants, (2) a notion of "connected" for set partitions / diagrams matching the physics definition, connecting Track A's pairings to Track B's partitions.

## Completed

(To be filled)
