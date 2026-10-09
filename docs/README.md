# Documentation guide

Use this guide to find the document for your task. Lean declarations are
authoritative for mathematical meaning; notes describe assumptions, current
design, and remaining work.

## Start here

| Goal | Read |
| --- | --- |
| Understand the project and contribution rules | [Project guide](../PROJECT.md) and [conventions](conventions.md) |
| Find a domain and its vocabulary | [Context map](../CONTEXT-MAP.md) |
| Understand physical models and assumptions | [Models and assumptions](model-and-assumptions.md) |
| Browse declarations | [Declaration Explorer](https://naoki-cpp.github.io/LeanCondensedMatter/) |
| Find current targets and proved milestones | [Roadmap](roadmap.md) and [completed targets](completed.md) |
| Understand design rationale | [Architecture decision records](adr/README.md) |

## Models, terminology, and examples

- [Models and assumptions](model-and-assumptions.md) — physical assumptions and the physics-to-Lean dictionary.
- [Caveats](caveats.md) — pitfalls and boundaries.
- [References](references.md) — annotated external sources.
- [Second-quantization terminology](glossary/second-quantization-terminology.md).
- [MassiveDirac transport vocabulary](../CONTEXT.md) — the finite-cutoff current-response subcontext.
- Worked examples:
  - [Finite response evaluation](examples/finite-response-evaluation.md).
  - [Free-fermion entropy](examples/free-fermion-entropy.md).
  - [Low-order fermionic linked-cluster theorem](examples/fermionic-lct-low-order.md).

## Current architecture

Architecture notes describe subsystem ownership and dependencies. The
[ADRs](adr/README.md) explain the decisions and trade-offs behind those boundaries.

- [Combinatorics and order decomposition](architecture/combinatorics-order-decomposition.md).
- [Quantum density theory](architecture/quantum-density-theory.md).
- [Physical real-scalar boundary](architecture/physical-real-scalar-boundary.md).
- [Second quantization](architecture/second-quantization.md).
- [Fermionic field operators](architecture/fermionic-field-operators.md).
- [Transport](architecture/transport.md).

## Research targets and status

Start with the [repository roadmap](roadmap.md) for status definitions
and cross-track targets. Follow these topic documents for details.

| Area | Topic documents |
| --- | --- |
| Cross-track structures | [Unifying mathematical structures (ideas)](roadmaps/unifying-structures.md) |
| Quantum theory | [Foundations](roadmaps/quantum-theory-foundations.md) |
| Combinatorics | [Combinatorics](roadmaps/combinatorics.md) |
| Operator analysis | [Operator algebra](roadmaps/operator-algebra.md), [Fredholm determinant](roadmaps/fredholm-determinant.md) |
| Second quantization | [Roadmap](roadmaps/second-quantization.md), [status](roadmaps/second-quantization-status.md), [completed-space and infinite-mode boundary](roadmaps/completed-space-and-infinite-mode.md) |
| Thermal and diagrammatic theory | [Thermal expectation architecture](roadmaps/thermal-expectation-architecture.md), [linked-cluster theorem](roadmaps/linked-cluster-theorem.md) |
| Transport and disorder | [Transport](roadmaps/transport.md), [impurity vertex correction](roadmaps/impurity-vertex-correction.md), [spin Hall](roadmaps/spin-hall.md) |

## Contributor and audit references

- [Conventions](conventions.md) — naming, documentation, proofs, dependencies, and PR workflow.
- [Reviewed simp boundaries](simp-boundaries.md).
- [Retained theorem-audit candidates](theorem-catalog-retained.md).
- [Analysis inventory against Mathlib](analysis-mathlib-audit.md).
- [Architecture audit tooling](../scripts/architecture/README.md).
- API migration references: [canonical theorem names](migrations/canonical-theorem-names.md) and [second-quantization R2 rollup](migrations/second-quantization-r2-rollup.md).
- Agent guidance: [domain navigation](agents/domain.md), [issue tracker](agents/issue-tracker.md), and [triage labels](agents/triage-labels.md).

## Where documentation lives

| Location | Role |
| --- | --- |
| [README.md](../README.md) | Public entry point and build command |
| [PROJECT.md](../PROJECT.md) | Shared project instruction entry point |
| [CONTEXT-MAP.md](../CONTEXT-MAP.md) | Domain scopes and language sources |
| [docs/adr/](adr/README.md) | Architecture decisions and rationale |
| [docs/](./) | Documentation guide, models, conventions, architecture, examples, research status, and audits |
| [docs-site/](../docs-site/) | Published Declaration Explorer assets |

When updating documentation, keep substantive content in the document that owns
it and link to it from this guide. Keep current design in architecture notes,
targets and limitations in roadmaps, and enduring decision rationale in ADRs.
