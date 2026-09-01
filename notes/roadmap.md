# Roadmap

Formalization targets and current status. Detailed ownership and open problems live in the per-track
roadmaps; major proved milestones are summarized in [`completed.md`](completed.md).

Status: `idea` = no stable statement, `stated` = interface fixed but incomplete, `proved` = compiles
without `sorry`.

## Tracks

```text
A  quantum theory          states, measurements, entropy, Gibbs theory
B  combinatorics           partitions, cumulants, connected structures
C  operator analysis       compact/spectral/trace/Hilbert–Schmidt tools
D  second quantization     Fock algebra, thermal states, Dyson and diagrams
E  transport/disorder      Kubo–Bastin/Středa, resolvents, disorder, Born/SCBA, models
```

## Targets

| Target | Track | Status | Details |
|---|---|---|---|
| Minimal bounded axiomatic quantum theory | A | `proved` | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#minimal-bounded-theory) |
| Canonical density operators and expectations | A/C | `proved` | [architecture](architecture/quantum-density-theory.md) |
| Canonical purity, bounds, pure-state value, and finite-dimensional trace formula | A/C | `proved` | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#density-operators-expectations-and-purity) |
| Maximal-purity rank-one characterization | A/C | `idea` | [quantum-theory open work](roadmaps/quantum-theory-foundations.md#open-work) |
| Countable discrete POVMs and Born normalization | A | `proved` | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#discrete-povms-and-born-probabilities) |
| Von Neumann entropy with finite-dimensional specialization | A/C | `proved` | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#von-neumann-entropy) |
| Finite free-fermion Gibbs entropy and Fermi–Dirac binary decomposition | A/D | `proved` | [worked example](examples/free-fermion-entropy.md) |
| Bounded Gibbs state, free-energy bound, Gibbs entropy identity, and minimizer uniqueness | A/C | `proved` under explicit compactness and summability hypotheses | [quantum-theory foundations](roadmaps/quantum-theory-foundations.md#gibbs-states-and-helmholtz-free-energy) |
| Unbounded Hamiltonian and genuine infinite-dimensional Gibbs theory | A/C | `idea` | [operator analysis](roadmaps/operator-algebra.md) |
| Partition-lattice refinement and Möbius factorization | B | `proved` | [combinatorics](roadmaps/combinatorics.md) |
| Explicit partition-lattice Möbius formula | B | `proved` | [combinatorics](roadmaps/combinatorics.md) |
| Moment–cumulant inversion | B | `proved` | [combinatorics](roadmaps/combinatorics.md) |
| Cumulants vanish across independence | B | `proved` | [combinatorics](roadmaps/combinatorics.md) |
| Formal-log coefficient / finite-set cumulant bridge | B | `proved` | `Combinatorics/PowerSeriesCumulant.lean` |
| Compact self-adjoint spectral decomposition | C | `proved` | [operator analysis](roadmaps/operator-algebra.md) |
| Spectral trace-class theory and trace identities | C | `proved` | [operator analysis](roadmaps/operator-algebra.md) |
| Hilbert–Schmidt basic, inner-product, and trace infrastructure | C | `proved` | [operator analysis](roadmaps/operator-algebra.md) |
| Countable diagonal infinite-dimensional Fredholm determinant | C | `proved` | [Fredholm determinant roadmap](roadmaps/fredholm-determinant.md) |
| General non-self-adjoint trace-class ideal | C | `idea` | [operator analysis](roadmaps/operator-algebra.md) |
| General Fredholm determinant | C | `idea` | [Fredholm determinant roadmap](roadmaps/fredholm-determinant.md#requirements-for-a-general-fredholm-determinant) |
| Generic bounded Dyson–Volterra theory | C/D | `proved` | `Analysis/Dyson/` |
| Finite-volume Kubo–Bastin and regularized Středa response chain | A/C/E | `proved` | [transport roadmap](roadmaps/transport.md#proved-clean-response-chain) |
| Exact finite-disorder averaged Green invertibility and canonical exact self-energy at nonzero broadening | C/E | `proved` | [transport roadmap](roadmaps/transport.md#proved-disorder-chain) |
| Physical conductivity bridge from response-level Středa data with explicit normalization and limits | E | `stated` | [transport architecture](architecture/transport.md#resolvent-and-response-boundary) |
| Trace-per-unit-volume / thermodynamic-limit transport | C/E | `idea` | [transport roadmap](roadmaps/transport.md#open-targets) |
| Generic algebraic second-quantization evolution and local-operator layer | D | `proved` | [second-quantization status](roadmaps/second-quantization-status.md) |
| Finite-mode fermionic thermal, Dyson, and partition-function linked-cluster line | D | `proved` | [linked cluster theorem](roadmaps/linked-cluster-theorem.md) |
| Finite-mode fermionic two-point linked-cluster theorem with external legs | D | `proved` | `SecondQuantization/Fermionic/Diagrammatics/TwoPointDiagramExpansion/CauchySeries.lean` |
| Finite-temperature Bloch–de Dominicis pairing recursion and finite Gibbs instance | A/D | `proved` | [thermal expectation architecture](roadmaps/thermal-expectation-architecture.md) |
| Bosonic algebraic and two-point thermal layer | D | `proved` for current stated results; general Gibbs/Dyson layer remains `idea` | [second-quantization status](roadmaps/second-quantization-status.md) |
| Convergence-aware bosonic Gibbs and perturbation theory | C/D | `idea` | [second quantization](roadmaps/second-quantization.md) |
| Completed fermionic free Fock/domain and thermal theory | C/D | `proved` under explicit boundedness, domain, and summability hypotheses | [completed-space boundary](roadmaps/completed-space-and-infinite-mode.md) |
| Completed bosonic, interacting completed-space, and thermodynamic-limit second quantization | C/D | `idea` | [completed-space boundary](roadmaps/completed-space-and-infinite-mode.md#open-work) |
| Higher time-ordered correlation functions, general source insertions, and multi-leg connected expansions | D | `idea` | [second quantization](roadmaps/second-quantization.md) |
