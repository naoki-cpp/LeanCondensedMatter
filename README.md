# LeanCondensedMatter

[![CI](https://github.com/naoki-cpp/LeanCondensedMatter/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/naoki-cpp/LeanCondensedMatter/actions/workflows/lean_action_ci.yml)
[![docs](https://img.shields.io/badge/docs-online-blue)](https://naoki-cpp.github.io/LeanCondensedMatter/docs/)

Formalizing results in condensed matter physics as machine-checked theorems in Lean 4, building on Mathlib.

The repository currently includes quantum-theory foundations, operator-analysis infrastructure,
combinatorics for cumulants and connected structures, algebraic second quantization, finite-temperature
fermionic thermal theory, quartic Wick/Dyson diagrammatics, formal and finite-dimensional analytic
Linked Cluster Theorems, and a finite-mode fermionic two-point linked-cluster theorem with external
legs.

## Documentation

- [PROJECT.md](PROJECT.md) — project purpose, documentation layout, and contribution rules.
- [notes/roadmap.md](notes/roadmap.md) — repository-wide targets and current status.
- [notes/completed.md](notes/completed.md) — major proved endpoints.
- [notes/architecture/second-quantization.md](notes/architecture/second-quantization.md) — enforced SecondQuantization ownership, dependency, and public-API boundaries.
- [notes/roadmaps/second-quantization-status.md](notes/roadmaps/second-quantization-status.md) — current SecondQuantization capabilities and research boundary.
- [notes/roadmaps/linked-cluster-theorem.md](notes/roadmaps/linked-cluster-theorem.md) — vacuum and two-point linked-cluster endpoints.
- [notes/model-and-assumptions.md](notes/model-and-assumptions.md) — physics-to-Lean dictionary and modeling assumptions.

Lean declarations and CI-enforced architecture checks are the source of truth when prose and code disagree.

## Building

```sh
lake build
```

## Proof reuse audit

To look for multi-line, explicitly typed `have ... : T := by` proofs that can be replaced by a shorter existing proof, run:

```sh
python scripts/proof_reuse_audit.py LeanCondensedMatter/Path/To/File.lean
```

The audit tries `exact?`, `apply? <;> assumption`, and `simp?` one block at a time in temporary copies of the file. It reports a candidate only when the modified file compiles, so each suggested replacement is checked by Lean in the original local context. Use `--json` for machine-readable output.
