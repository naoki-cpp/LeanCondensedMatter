# Architecture decision records

These records state the architectural decisions embodied in the current repository and the trade-offs that constrain its extension. They were reconstructed from the implementation and existing design documentation; they do not claim to reproduce historical discussions, decision dates, or the order in which decisions were made. Numbering is for reference.

All records in this initial set have status **accepted**, meaning implemented in the current design. Alternatives mentioned explain the present trade-off, not an undocumented historical evaluation.

## Foundations and module ownership

- [0001 — Use Lean and Mathlib as the mathematical foundation](0001-lean-and-mathlib.md)
- [0002 — Assign modules by semantic responsibility](0002-semantic-ownership.md)
- [0010 — Use Lean for semantic guarantees and source audits for architecture](0010-verification-boundaries.md)

## States, measurements, and thermal structure

- [0003 — Use one density-state model across dimensions](0003-density-backed-states.md)
- [0004 — Preserve reality and positivity at physical scalar boundaries](0004-physical-scalar-types.md)
- [0015 — Normalize countable discrete measurements pointwise](0015-countable-discrete-povms.md)
- [0016 — Normalize heat data before constructing the Gibbs state](0016-heat-operator-first-gibbs-states.md)

## Second quantization and diagrammatics

- [0005 — Separate algebraic Fock constructions from analytic realizations](0005-fock-representations.md)
- [0006 — Separate thermal states from the pairing recursion](0006-thermal-expectation-recursion.md)
- [0007 — Make bosonic thermal summability a domain condition](0007-bosonic-summability-domains.md)
- [0008 — Separate diagram combinatorics, physical amplitudes, and convergence](0008-diagrammatics-and-analysis.md)

## Operators and spectral geometry

- [0011 — Define bounded operator functions through functional calculus](0011-functional-calculus.md)
- [0012 — Reconstruct compact self-adjoint operators on their nonzero spectral support](0012-nonzero-spectral-support.md)
- [0013 — Construct discrete heat operators from summable spectral weights](0013-diagonal-heat-operator.md)
- [0014 — Keep operator ideals and determinants within proved domains](0014-operator-ideals-and-fredholm-determinants.md)
- [0018 — Keep finite-band Berry geometry upstream of physical models](0018-finite-band-berry-geometry.md)

## Response and crystal structure

- [0009 — Keep generic response separate from physical conductivity and models](0009-response-and-conductivity.md)
- [0017 — Derive crystal structure from weak atomic configurations](0017-crystal-from-atomic-configurations.md)

[Historical review coverage](history-review.md) tracks the issue-focused sequential review, records PR-only number gaps as skips, and identifies the next issue to inspect. Historical evidence sections distinguish recorded motivations from current implementation constraints.

Lean declarations are authoritative for mathematical meaning. [Architecture notes](../../notes/architecture/) describe the current subsystem layout, [roadmaps](../../notes/roadmap.md) describe targets and remaining work, and these ADRs explain why the enduring boundaries exist. An ADR is not a proof milestone or a replacement for those documents.

Add a new sequentially numbered record when a consequential design decision changes these boundaries. Mark a replaced decision as superseded and link its successor; keep the active decision and current architecture notes consistent. Do not add retrospective timestamps or implementation logs.
