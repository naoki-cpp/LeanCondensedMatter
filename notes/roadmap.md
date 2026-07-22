# Roadmap

Formalization targets and their status, at a glance. Details live in per-track files;
completed targets move to `notes/completed.md`.

Status values: `idea` → `stated` (definition/statement written, may contain `sorry`) → `proved` (compiles, no `sorry`).

## Approach

The Linked Cluster Theorem target rests on four largely independent prerequisite tracks that all feed into it. Work on the tracks can proceed in parallel; the top-level theorem waits on all four. Track C is a foundational gap discovered while scoping Track A's extension to the countably-infinite-dimensional (Fock space) setting: Mathlib currently has no trace-class/Schatten-class operator theory, so `DensityOperator`/`vonNeumannEntropy`/`gibbsState` are finite-dimensional only (see `notes/caveats.md`). Track D (second quantization) is the concrete algebraic build-out of Track A's former "QFT groundwork" placeholder.

```
Track A: quantum theory     Track B: combinatorics       Track C: operator algebra      Track D: second quantization
  Bloch-de Dominicis thm.     Partition lattice ->         Bounded -> compact ->          Mode -> fermion occupation ->
                                Möbius factorization ->      Hilbert-Schmidt -> trace-      Fock space -> creation/
                                moment-cumulant inversion     class -> Fredholm det.        annihilation -> CAR -> ...
                                                                                            (bosonic line in parallel)
              \                        /                            /                              /
               \                      /                            /                              /
                -> Linked Cluster Theorem (finite temperature) <---------------------------------
```

Track B has grown from "combinatorial auxiliary for the Linked Cluster Theorem" into an independent,
reusable Lean library (`Combinatorics/`: partition lattice, incidence algebra, Möbius inversion) —
plausibly of independent interest for a future Mathlib contribution, not just infrastructure for
Track D.

## Targets

| Target | Track | Status | Details |
|---|---|---|---|
| Minimal axiomatic quantum theory foundation | A | `stated` | [notes/roadmaps/quantum-theory-foundations.md](roadmaps/quantum-theory-foundations.md#minimal-axiomatic-quantum-theory-foundation) |
| Density operators and the Born rule (finite-dimensional) | A | `stated` | [notes/roadmaps/quantum-theory-foundations.md](roadmaps/quantum-theory-foundations.md#density-operators-and-the-born-rule-finite-dimensional) |
| Von Neumann entropy / Boltzmann's principle (finite-dimensional) | A | `stated` | [notes/roadmaps/quantum-theory-foundations.md](roadmaps/quantum-theory-foundations.md#von-neumann-entropy--boltzmanns-principle-finite-dimensional) |
| Canonical distribution as the Helmholtz free-energy-minimizing state | A | `stated` | [notes/roadmaps/quantum-theory-foundations.md](roadmaps/quantum-theory-foundations.md#canonical-distribution-as-the-helmholtz-free-energy-minimizing-state) |
| Finite-temperature many-body perturbation theory (formerly "basic QFT") | A | `idea` | [notes/roadmaps/quantum-theory-foundations.md](roadmaps/quantum-theory-foundations.md#basic-quantum-field-theory-formalization) |
| Finite-temperature Bloch–de Dominicis theorem | A | `idea` | [notes/roadmaps/quantum-theory-foundations.md](roadmaps/quantum-theory-foundations.md#finite-temperature-bloch–de-dominicis-theorem) |
| Partition-lattice refinement/Möbius factorization | B | `proved` | [notes/roadmaps/combinatorics.md](roadmaps/combinatorics.md#partition-lattice-möbius--moment-cumulant-formula) |
| Explicit partition-lattice Möbius formula (`(-1)^(n-1)(n-1)!`) | B | `stated` | [notes/roadmaps/combinatorics.md](roadmaps/combinatorics.md#partition-lattice-möbius--moment-cumulant-formula) |
| Moment–cumulant inversion formula | B | `proved` | [notes/roadmaps/combinatorics.md](roadmaps/combinatorics.md#moment–cumulant-inversion) |
| Cumulants vanish across independence (moment factorization + cumulant vanishing) | B | `proved` | [notes/roadmaps/combinatorics.md](roadmaps/combinatorics.md#cumulants-vanish-across-independence) |
| Bounded/compact operator groundwork | C | `proved` | [notes/roadmaps/operator-algebra.md](roadmaps/operator-algebra.md#continuous-functional-calculus-acts-on-eigenvectors-by-evaluation) |
| Hilbert–Schmidt operator theory | C | `stated` | [notes/roadmaps/operator-algebra.md](roadmaps/operator-algebra.md#hilbert–schmidt-operators) |
| Trace-class operator theory | C | `stated` | [notes/roadmaps/operator-algebra.md](roadmaps/operator-algebra.md#trace-class--hilbert-schmidt-operator-theory) |
| Fredholm determinant | C | `idea` | [notes/roadmaps/operator-algebra.md](roadmaps/operator-algebra.md) |
| Second quantization, fermionic primary line (Fock space, CAR, Hamiltonians, Dyson expansion) | D | `stated` (phases 1-7 done; phase 9 in progress — the general finite-temperature n-point Bloch–de Dominicis theorem is proved (`Common/BlochDeDominicis/Induction.lean`), with its combinatorial recursion extracted as a reusable abstract theorem (`Combinatorics/PerfectPairing/FirstPairRecursion.lean`); the genuine interaction-picture Dyson series (step 5) is done; diagram connectedness (step 6) is in progress, with its abstract moment-cumulant bridge proved (`Combinatorics/DiagramConnectedness.lean`); the linked-cluster bridge move (step 7) is not yet started) | [notes/roadmaps/second-quantization.md](roadmaps/second-quantization.md) |
| Second quantization, bosonic line (parallel, not critical path) | D | `stated` (occupation done) | [notes/roadmaps/second-quantization.md](roadmaps/second-quantization.md#bosonic-line-parallel-not-critical-path) |
| Linked Cluster Theorem (finite temperature) | Combined | `idea` | [notes/roadmaps/linked-cluster-theorem.md](roadmaps/linked-cluster-theorem.md#linked-cluster-theorem-finite-temperature) |

See [notes/completed.md](completed.md) for targets that have reached `proved`.
