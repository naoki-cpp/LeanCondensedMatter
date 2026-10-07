# Documentation guide

Use this guide to find the document for your task. Lean declarations are
authoritative for mathematical meaning; notes describe assumptions, current
design, and remaining work.

## Start here

| Goal | Read |
| --- | --- |
| Understand the project and contribution rules | [Project guide](../PROJECT.md) and [conventions](../notes/conventions.md) |
| Find a domain and its vocabulary | [Context map](../CONTEXT-MAP.md) |
| Understand physical models and assumptions | [Models and assumptions](../notes/model-and-assumptions.md) |
| Browse declarations | [Declaration Explorer](https://naoki-cpp.github.io/LeanCondensedMatter/) |
| Find current targets and proved milestones | [Roadmap](../notes/roadmap.md) and [completed targets](../notes/completed.md) |
| Understand design rationale | [Architecture decision records](../doc/adr/README.md) |

## Models, terminology, and examples

- [Models and assumptions](../notes/model-and-assumptions.md) — physical assumptions and the physics-to-Lean dictionary.
- [Caveats](../notes/caveats.md) — pitfalls and boundaries.
- [References](../notes/references.md) — annotated external sources.
- [Second-quantization terminology](../notes/glossary/second-quantization-terminology.md).
- [MassiveDirac transport vocabulary](../CONTEXT.md) — the finite-cutoff current-response subcontext.
- Worked examples:
  - [Finite response evaluation](../notes/examples/finite-response-evaluation.md).
  - [Free-fermion entropy](../notes/examples/free-fermion-entropy.md).
  - [Low-order fermionic linked-cluster theorem](../notes/examples/fermionic-lct-low-order.md).

## Current architecture

Architecture notes describe subsystem ownership and dependencies. The
[ADRs](../doc/adr/README.md) explain the decisions and trade-offs behind those boundaries.

- [Combinatorics and order decomposition](../notes/architecture/combinatorics-order-decomposition.md).
- [Quantum density theory](../notes/architecture/quantum-density-theory.md).
- [Physical real-scalar boundary](../notes/architecture/physical-real-scalar-boundary.md).
- [Second quantization](../notes/architecture/second-quantization.md).
- [Fermionic field operators](../notes/architecture/fermionic-field-operators.md).
- [Transport](../notes/architecture/transport.md).

## Research targets and status

Start with the [repository roadmap](../notes/roadmap.md) for status definitions
and cross-track targets. Follow these topic documents for details.

| Area | Topic documents |
| --- | --- |
| Quantum theory | [Foundations](../notes/roadmaps/quantum-theory-foundations.md) |
| Combinatorics | [Combinatorics](../notes/roadmaps/combinatorics.md) |
| Operator analysis | [Operator algebra](../notes/roadmaps/operator-algebra.md), [Fredholm determinant](../notes/roadmaps/fredholm-determinant.md) |
| Second quantization | [Roadmap](../notes/roadmaps/second-quantization.md), [status](../notes/roadmaps/second-quantization-status.md), [completed-space and infinite-mode boundary](../notes/roadmaps/completed-space-and-infinite-mode.md) |
| Thermal and diagrammatic theory | [Thermal expectation architecture](../notes/roadmaps/thermal-expectation-architecture.md), [linked-cluster theorem](../notes/roadmaps/linked-cluster-theorem.md) |
| Transport and disorder | [Transport](../notes/roadmaps/transport.md), [impurity vertex correction](../notes/roadmaps/impurity-vertex-correction.md), [spin Hall](../notes/roadmaps/spin-hall.md) |

## Contributor and audit references

- [Conventions](../notes/conventions.md) — naming, documentation, proofs, dependencies, and PR workflow.
- [Reviewed simp boundaries](../notes/simp-boundaries.md).
- [Retained theorem-audit candidates](../notes/theorem-catalog-retained.md).
- [Analysis inventory against Mathlib](analysis-mathlib-audit.md).
- [Architecture audit tooling](../scripts/architecture/README.md).
- API migration references: [canonical theorem names](../notes/migrations/canonical-theorem-names.md) and [second-quantization R2 rollup](../notes/migrations/second-quantization-r2-rollup.md).
- Agent guidance: [domain navigation](agents/domain.md), [issue tracker](agents/issue-tracker.md), and [triage labels](agents/triage-labels.md).

## Where documentation lives

| Location | Role |
| --- | --- |
| [README.md](../README.md) | Public entry point and build command |
| [PROJECT.md](../PROJECT.md) | Shared project instruction entry point |
| [CONTEXT-MAP.md](../CONTEXT-MAP.md) | Domain scopes and language sources |
| [notes/](../notes/) | Models, conventions, architecture, examples, and research status |
| [doc/adr/](../doc/adr/README.md) | Architecture decisions and rationale |
| [docs/](./) | This navigation guide, agent guidance, and analysis audit |
| [docs-site/](../docs-site/) | Published Declaration Explorer assets |

When updating documentation, keep substantive content in the document that owns
it and link to it from this guide. Keep current design in architecture notes,
targets and limitations in roadmaps, and enduring decision rationale in ADRs.
