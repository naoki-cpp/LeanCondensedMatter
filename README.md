# LeanCondensedMatter

[![CI](https://github.com/naoki-cpp/LeanCondensedMatter/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/naoki-cpp/LeanCondensedMatter/actions/workflows/lean_action_ci.yml)
[![declaration explorer](https://img.shields.io/badge/declaration%20explorer-online-blue)](https://naoki-cpp.github.io/LeanCondensedMatter/)

Formalizing results in condensed matter physics as machine-checked theorems in Lean 4, building on Mathlib.

The repository currently includes quantum-theory foundations, operator-analysis infrastructure,
combinatorics for cumulants and connected structures, algebraic second quantization, finite-temperature
fermionic thermal theory, quartic Wick/Dyson diagrammatics, formal and finite-dimensional analytic
Linked Cluster Theorems, a statistics-independent normalized moment/connected-decomposition core,
finite-volume response theory, and
massive-Dirac continuum/disorder transport with a finite-mode fermionic two-point linked-cluster
theorem with external legs.

## Highlighted canonical endpoints

Representative public theorems include:

- `Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution` — statistics-independent formal-log / connected-decomposition bridge;
- `Combinatorics.NormalizedSetFunction.moment_cumulant` — reconstruction of normalized finite-set moments from cumulants;
- `SecondQuantization.Common.BlochDeDominicis.finiteGibbsExpectation_prod_eq_sum_pairing` — finite-temperature Bloch–de Dominicis pairing;
- `SecondQuantization.Fermionic.factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude` — formal finite-mode linked-cluster theorem;
- `SecondQuantization.Fermionic.iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude` — analytic finite-dimensional linked-cluster theorem;
- `SecondQuantization.Fermionic.vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries` — finite-mode two-point linked-cluster theorem.

The theorem catalog and subsystem notes are the authoritative navigation surfaces for the full public API.

## Documentation

- [Declaration Explorer](https://naoki-cpp.github.io/LeanCondensedMatter/) — interactive project-area, module, theorem, dependency, and consumer navigation; theorem data comes from the compiled catalog and module descriptions come from umbrella-module documentation.
- [PROJECT.md](PROJECT.md) — project purpose, documentation layout, and contribution rules.
- [notes/roadmap.md](notes/roadmap.md) — repository-wide targets and current status.
- [notes/completed.md](notes/completed.md) — major proved endpoints.
- [notes/architecture/second-quantization.md](notes/architecture/second-quantization.md) — enforced SecondQuantization ownership, dependency, and public-API boundaries.
- [notes/roadmaps/second-quantization-status.md](notes/roadmaps/second-quantization-status.md) — current SecondQuantization capabilities and research boundary.
- [notes/roadmaps/linked-cluster-theorem.md](notes/roadmaps/linked-cluster-theorem.md) — partition-function and two-point linked-cluster endpoints.
- [notes/model-and-assumptions.md](notes/model-and-assumptions.md) — physics-to-Lean dictionary and modeling assumptions.
- [notes/migrations/](notes/migrations/) — concise migration notes for deliberate breaking public-API changes.

Lean declarations and CI-enforced architecture checks are the source of truth when prose and code disagree.

Transport ownership and normalization boundaries are documented in
[notes/architecture/transport.md](notes/architecture/transport.md), with proved chains and open
targets tracked in [notes/roadmaps/transport.md](notes/roadmaps/transport.md).

## Building

```sh
lake build
```
