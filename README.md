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

To look for proof regions that can be replaced by a shorter existing proof, run:

```sh
python scripts/proof_reuse_audit.py LeanCondensedMatter/Path/To/File.lean
```

The audit scans complete explicitly typed `have ... : T := by` bodies and contiguous top-level tactic intervals inside theorem, lemma, example, `have`, and `haveI` proofs. For each region it uses `exact?`, `apply?`, and `simp?` only to discover concrete `Try this:` suggestions, then inserts each concrete suggestion into a fresh temporary copy and recompiles the whole file. Suggestions containing proof holes, `sorry`, or search scaffolding are rejected, and replay output must be admission-free before a replacement is reported.

Findings are ranked as project-theorem reuse, other theorem reuse, then automation compression. If `docs/generated/theorems.json` is present, the audit uses it to identify project theorems by unique qualified-name suffix; otherwise the audit still runs and reports the theorem origin as unknown. Generate the catalog with `lake env lean scripts/TheoremCatalog.lean` when project-theorem classification is needed. Interval search and suggestion replay are bounded by default; use `--max-span-tactics`, `--max-intervals-per-block`, `--max-suggestions-per-search`, or `--no-intervals` to tune them, and `--json` for machine-readable output.
