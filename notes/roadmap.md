# Roadmap

Formalization targets and their status, at a glance. Details live in per-track files; major completed
targets are also recorded in [`completed.md`](completed.md).

Status values: `idea` → `stated` (definition/statement written, may contain `sorry`) → `proved`
(compiles, no `sorry`).

## Approach

The project develops four interacting tracks:

```text
Track A: quantum theory     Track B: combinatorics       Track C: operator algebra      Track D: second quantization
  axioms and thermal states   partitions and cumulants     compact/trace-class tools      Fock space, CAR/CCR,
                                                                                          Dyson and diagrams
               \                        /                            /                              /
                \                      /                            /                              /
                 -> finite-temperature many-body theorems <---------------------------------------
```

Track B has become an independent reusable Lean combinatorics library. Track D now contains a
completed finite-mode, formal/algebraic fermionic Dyson Linked Cluster Theorem. The remaining LCT work
is analytic interpretation, correlation-function extensions, bosonic convergence-aware interfaces,
and infinite-dimensional operator theory.

## Targets

| Target | Track | Status | Details |
|---|---|---|---|
| Minimal axiomatic quantum theory foundation | A | `stated` | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#minimal-axiomatic-quantum-theory-foundation) |
| Density operators and the Born rule (finite-dimensional) | A | `stated` | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#density-operators-and-the-born-rule-finite-dimensional) |
| Von Neumann entropy / Boltzmann's principle (finite-dimensional) | A | `stated` | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#von-neumann-entropy--boltzmanns-principle-finite-dimensional) |
| Canonical distribution as the Helmholtz free-energy-minimizing state | A | `stated` | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#canonical-distribution-as-the-helmholtz-free-energy-minimizing-state) |
| Finite-temperature many-body perturbation theory | A/D | `stated` — coefficientwise finite-mode Dyson theory is proved; analytic convergence and equality with the interacting partition function remain | [second quantization](roadmaps/second-quantization.md) |
| Finite-temperature Bloch–de Dominicis theorem | A/D | `proved` in the abstract finite-basis setting, with fermionic and bosonic two-point specializations | [second-quantization status](roadmaps/second-quantization-status.md) |
| Partition-lattice refinement/Möbius factorization | B | `proved` | [combinatorics](roadmaps/combinatorics.md#partition-lattice-möbius--moment-cumulant-formula) |
| Explicit partition-lattice Möbius formula `(-1)^(n-1)(n-1)!` | B | `stated` | [combinatorics](roadmaps/combinatorics.md#partition-lattice-möbius--moment-cumulant-formula) |
| Moment–cumulant inversion formula | B | `proved` | [combinatorics](roadmaps/combinatorics.md#moment–cumulant-inversion) |
| Cumulants vanish across independence | B | `proved` | [combinatorics](roadmaps/combinatorics.md#cumulants-vanish-across-independence) |
| Formal-log coefficient / finite-set cumulant bridge | B | `proved` | `Combinatorics/PowerSeriesCumulant.lean` |
| Bounded/compact operator groundwork | C | `proved` | [operator algebra](roadmaps/operator-algebra.md#continuous-functional-calculus-acts-on-eigenvectors-by-evaluation) |
| Hilbert–Schmidt operator theory | C | `stated` | [operator algebra](roadmaps/operator-algebra.md#hilbert–schmidt-operators) |
| Trace-class operator theory | C | `stated` | [operator algebra](roadmaps/operator-algebra.md#trace-class--hilbert-schmidt-operator-theory) |
| Fredholm determinant | C | `idea` | [operator algebra](roadmaps/operator-algebra.md) |
| Second quantization, fermionic finite-mode algebraic line | D | `proved` — Fock/CAR, thermal theory, Dyson coefficients, full quartic Wick diagrams, component factorization, connected cumulants, and the algebraic Dyson LCT are complete | [current status](roadmaps/second-quantization-status.md#fermionic-line) · [development roadmap](roadmaps/second-quantization.md) |
| Second quantization, bosonic parallel line | D | `stated` — algebraic, free thermal, two-point Bloch–de Dominicis, and quartic component data are proved; general Gibbs/Dyson/amplitude layers remain convergence-limited | [current status](roadmaps/second-quantization-status.md#bosonic-line) · [development roadmap](roadmaps/second-quantization.md#bosonic-parallel-line) |
| Fermionic Dyson Linked Cluster Theorem, formal/algebraic finite-mode form | Combined | `proved` | [completed roadmap](roadmaps/linked-cluster-theorem.md) · `SecondQuantization.factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude` |
| Analytic finite-dimensional Dyson/partition-function connection | D | `idea` | [next phases](roadmaps/second-quantization.md#f2--analytic-finite-dimensional-dyson-theorem) |
| Connected time-ordered correlation-function expansion | D | `idea` | [next phases](roadmaps/second-quantization.md#f3--correlation-functions-and-external-legs) |

See [`completed.md`](completed.md) for a compact list of major targets that have reached `proved`.
