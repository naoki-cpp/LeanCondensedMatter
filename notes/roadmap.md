# Roadmap

Formalization targets and their current status. Detailed ownership and open problems live in the
per-track roadmaps; completed milestones are summarized in [`completed.md`](completed.md).

Status values:

- `idea`: no stable formal statement yet;
- `stated`: a target or interface is fixed, but the intended theorem set is incomplete;
- `proved`: the stated target compiles without `sorry`.

## Tracks

```text
Track A: quantum theory     Track B: combinatorics       Track C: operator analysis      Track D: second quantization
states, measurements,        partitions, cumulants,       compact, spectral trace,         Fock algebra, thermal states,
entropy, Gibbs theory        connected structures         Hilbert–Schmidt tools            Dyson and diagrams
```

The tracks meet in finite-temperature many-body theorems. The current public density-state and
thermal expectation architecture is dimension-independent; finite-dimensional results are
specializations, not parallel APIs.

## Targets

| Target | Track | Status | Details |
|---|---|---|---|
| Minimal bounded axiomatic quantum theory | A | `proved` | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#minimal-axiomatic-quantum-theory) |
| Canonical density operators and expectations | A/C | `proved` | [architecture](architecture/quantum-density-theory.md) |
| Canonical purity, bounds, pure-state value, and finite-dimensional trace formula | A/C | `proved` | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#density-operators-expectations-and-purity) |
| Maximal-purity rank-one characterization | A/C | `idea` | [quantum-theory next steps](roadmaps/quantum-theory-foundations.md#current-next-steps) |
| Countable discrete POVMs and Born normalization | A | `proved` | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#discrete-povms-and-the-born-rule) |
| Von Neumann entropy with finite-dimensional specialization | A/C | `proved` | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#von-neumann-entropy) |
| Finite free-fermion Gibbs entropy and Fermi–Dirac binary decomposition | A/D | `proved` | [worked example](examples/free-fermion-entropy.md) |
| Bounded Gibbs state, free-energy bound, and Gibbs entropy identity | A/C | `proved` under explicit compactness and summability hypotheses | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#gibbs-states-and-helmholtz-free-energy) |
| Uniqueness of the Gibbs free-energy minimizer | A | `idea` | [quantum-theory next steps](roadmaps/quantum-theory-foundations.md#current-next-steps) |
| Unbounded Hamiltonian and genuine infinite-dimensional Gibbs theory | A/C | `idea` | [operator algebra](roadmaps/operator-algebra.md#unbounded-and-completed-space-boundary) |
| Partition-lattice refinement and Möbius factorization | B | `proved` | [combinatorics](roadmaps/combinatorics.md) |
| Explicit partition-lattice Möbius formula | B | `proved` | [combinatorics](roadmaps/combinatorics.md) |
| Moment–cumulant inversion | B | `proved` | [combinatorics](roadmaps/combinatorics.md) |
| Cumulants vanish across independence | B | `proved` | [combinatorics](roadmaps/combinatorics.md) |
| Formal-log coefficient / finite-set cumulant bridge | B | `proved` | `Combinatorics/PowerSeriesCumulant.lean` |
| Compact self-adjoint spectral decomposition | C | `proved` | [operator algebra](roadmaps/operator-algebra.md#compact-self-adjoint-spectral-tools) |
| Spectral trace-class theory and trace identities | C | `proved` | [operator algebra](roadmaps/operator-algebra.md#spectral-trace-class-operators) |
| Hilbert–Schmidt basic, inner-product, and trace infrastructure | C | `proved` | [operator algebra](roadmaps/operator-algebra.md#hilbert–schmidt-operators) |
| Countable diagonal infinite-dimensional Fredholm determinant | C | `proved` | [Fredholm determinant roadmap](roadmaps/fredholm-determinant.md) · #659 |
| General non-self-adjoint trace-class ideal | C | `idea` | [operator algebra](roadmaps/operator-algebra.md#remaining-operator-analysis) |
| General Fredholm determinant | C | `idea` | [Fredholm determinant roadmap](roadmaps/fredholm-determinant.md#dependency-graph-for-a-general-fredholm-determinant) |
| Generic bounded Dyson–Volterra theory | C/D | `proved` | `Analysis/Dyson/` |
| Generic algebraic second-quantization evolution and local-operator layer | D | `proved` | [second-quantization status](roadmaps/second-quantization-status.md) |
| Finite-mode fermionic thermal, Dyson, and vacuum linked-cluster line | D | `proved` | [linked cluster theorem](roadmaps/linked-cluster-theorem.md) |
| Finite-mode fermionic two-point linked-cluster theorem with external legs | D | `proved` | `SecondQuantization/Fermionic/Diagrammatics/TwoPointDiagramExpansion/CauchySeries.lean` |
| Finite-temperature Bloch–de Dominicis pairing recursion and finite Gibbs instance | A/D | `proved` | [thermal expectation architecture](roadmaps/thermal-expectation-architecture.md) |
| Bosonic algebraic and two-point thermal layer | D | `proved` for current stated results; general Gibbs/Dyson layer remains `idea` | [second-quantization status](roadmaps/second-quantization-status.md) |
| Convergence-aware bosonic Gibbs and perturbation theory | C/D | `idea` | [second quantization](roadmaps/second-quantization.md) |
| Completed-space and infinite-mode second quantization | C/D | `stated` | [completed-space boundary](roadmaps/completed-space-and-infinite-mode.md) |
| Higher time-ordered correlation functions, general source insertions, and multi-leg connected expansions | D | `idea` | [second quantization](roadmaps/second-quantization.md) |

See [`completed.md`](completed.md) for the compact list of major proved milestones.
