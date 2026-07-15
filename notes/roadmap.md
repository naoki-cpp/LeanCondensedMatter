# Roadmap

Formalization targets and their status, at a glance. Details live in per-track files;
completed targets move to `notes/completed.md`.

Status values: `idea` → `stated` (definition/statement written, may contain `sorry`) → `proved` (compiles, no `sorry`).

## Approach

The Linked Cluster Theorem target rests on four largely independent prerequisite tracks that all feed into it. Work on the tracks can proceed in parallel; the top-level theorem waits on all four. Track C is a foundational gap discovered while scoping Track A's extension to the countably-infinite-dimensional (Fock space) setting: Mathlib currently has no trace-class/Schatten-class operator theory, so `DensityOperator`/`vonNeumannEntropy`/`gibbsState` are finite-dimensional only (see `notes/caveats.md`). Track D (second quantization) is the concrete algebraic build-out of Track A's former "QFT groundwork" placeholder.

```
Track A: quantum theory     Track B: combinatorics       Track C: operator algebra      Track D: second quantization
  Bloch-de Dominicis thm.     Partition-lattice Möbius /    (trace-class / Hilbert-        Fock space -> creation/annihilation
                                moment-cumulant formula      Schmidt, infinite-dim)         -> CCR -> Hamiltonians -> Dyson exp.
              \                        /                            /                              /
               \                      /                            /                              /
                -> Linked Cluster Theorem (finite temperature) <---------------------------------
```

## Targets

| Target | Track | Status | Details |
|---|---|---|---|
| Minimal axiomatic quantum theory foundation | A | `stated` | [notes/roadmaps/quantum-theory-foundations.md](roadmaps/quantum-theory-foundations.md#minimal-axiomatic-quantum-theory-foundation) |
| Density operators and the Born rule (finite-dimensional) | A | `stated` | [notes/roadmaps/quantum-theory-foundations.md](roadmaps/quantum-theory-foundations.md#density-operators-and-the-born-rule-finite-dimensional) |
| Von Neumann entropy / Boltzmann's principle (finite-dimensional) | A | `stated` | [notes/roadmaps/quantum-theory-foundations.md](roadmaps/quantum-theory-foundations.md#von-neumann-entropy--boltzmanns-principle-finite-dimensional) |
| Canonical distribution as the Helmholtz free-energy-minimizing state | A | `stated` | [notes/roadmaps/quantum-theory-foundations.md](roadmaps/quantum-theory-foundations.md#canonical-distribution-as-the-helmholtz-free-energy-minimizing-state) |
| Basic quantum field theory formalization | A | `idea` | [notes/roadmaps/quantum-theory-foundations.md](roadmaps/quantum-theory-foundations.md#basic-quantum-field-theory-formalization) |
| Finite-temperature Bloch–de Dominicis theorem | A | `idea` | [notes/roadmaps/quantum-theory-foundations.md](roadmaps/quantum-theory-foundations.md#finite-temperature-bloch–de-dominicis-theorem) |
| Partition-lattice Möbius / moment-cumulant formula | B | `stated` | [notes/roadmaps/combinatorics.md](roadmaps/combinatorics.md#partition-lattice-möbius--moment-cumulant-formula) |
| Trace-class / Hilbert-Schmidt operator theory | C | `stated` | [notes/roadmaps/operator-algebra.md](roadmaps/operator-algebra.md#trace-class--hilbert-schmidt-operator-theory) |
| Second quantization (Fock space, CCR, Hamiltonians, Dyson expansion) | D | `idea` | [notes/roadmaps/second-quantization.md](roadmaps/second-quantization.md) |
| Linked Cluster Theorem (finite temperature) | Combined | `idea` | [notes/roadmaps/linked-cluster-theorem.md](roadmaps/linked-cluster-theorem.md#linked-cluster-theorem-finite-temperature) |

See [notes/completed.md](completed.md) for targets that have reached `proved`.
