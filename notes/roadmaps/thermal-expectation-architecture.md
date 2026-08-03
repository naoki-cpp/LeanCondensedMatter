# Thermal expectation and Bloch–de Dominicis architecture

This document records the ownership boundary established by issue #421. It is the source of truth
for how normalized thermal expectations, finite occupation-basis formulas, and the generic
Bloch–de Dominicis pairing induction fit together.

The refactor is deliberately breaking. Superseded Gibbs-functional abstractions, forwarding names,
and compatibility imports are removed rather than retained.

## Canonical normalized expectation

The physical normalized expectation API is owned by the trace-class density state:

```lean
QuantumTheory.TraceClass.DensityOperator.expectation
    (ρ : DensityOperator H) : (H →L[ℂ] H) →L[ℂ] ℂ
```

This is the canonical public abstraction for bounded observables. Its API supplies complex
linearity, normalization, contractivity, finite/diagonal formulas, positivity for positive
observables, and reality for symmetric or self-adjoint observables.

Finite SecondQuantization uses

```lean
FiniteHilbertFock Config := EuclideanSpace ℂ Config
```

and transports algebraic-Fock endomorphisms to bounded Hilbert-space operators through
`finiteHilbertOperatorAlgHom`. The normalized finite Gibbs state is
`finiteGibbsDensityOperator`; `finiteGibbsExpectation` is its expectation after this transport.

## Finite trace-ratio realization

For finite configuration spaces, the normalized expectation is related to the physical trace ratio

```text
Tr[e^{-βH₀} A] / Tr[e^{-βH₀}]
```

by `finiteGibbsExpectation_eq_trace_div` in
`Common/Thermal/BlochDeDominicis/GibbsExpectation/Core.lean`.

The normalized Bloch–de Dominicis proofs use this trace-ratio formula. They do not use the temporary
normalized occupation-basis functional as their state abstraction.

## Occupation-basis proof infrastructure

Explicit finite sums remain useful when the coordinate formula itself is the mathematical content.
Their ownership is split as follows:

| Layer | Module | Responsibility |
|---|---|---|
| Generic diagonal trace | `Common/Thermal/DiagonalTrace.lean` | Matrix coefficients, finite composition/extensionality, and summability-aware `tsumTrace`. |
| Finite unnormalized sums | `Common/Thermal/FiniteWeightedTrace.lean` | `traceFock`, `weightedTrace`, and `weightSum`. |
| Normalized finite coordinate formula | `Common/Thermal/WeightedDiagonalFunctional.lean` | Temporary `normalizedWeightedDiagonal` formulas used only by explicit finite-sum proofs. |
| Density/coordinate comparison | `Common/Thermal/FiniteGibbsOccupationBasisBridge.lean` | Opt-in bridge from the canonical finite Gibbs state to the normalized occupation-basis sum. |

The occupation-basis bridge is intentionally explicit. Importing the canonical finite Gibbs state or
the generic Bloch–de Dominicis theorem must not silently expose the temporary coordinate
implementation.

Raw sums remain appropriate for matrix-coefficient identities, partition-function factorizations,
weighted-trace calculations, and proofs of finite expectation bridges. They are not competing
physical-state abstractions.

## Generic normalized pairing recursion

The arbitrary-length pairing induction is owned by
`Common/Thermal/BlochDeDominicis/ExpectationRecursion.lean`.

```lean
ExpectationPairingRecursion Operator s
```

contains only the data needed by the induction:

- expectation of an ordered operator list;
- normalized two-operator pair values;
- an admissibility predicate;
- normalization of the empty product;
- admissibility after deleting a pair;
- the KMS/exchange first-pair recurrence.

`ExpectationPairingRecursion.expectation_eq_sum_pairing` derives the weighted pairing expansion from
this contract. It has no configuration type, no `Fintype` assumption, no occupation basis, no trace,
and no density-operator implementation.

The `admissible` predicate is where an implementation records its actual analytic obligations. A
future bosonic implementation may include summability, integrability, closure under products, and
domain hypotheses there without changing the combinatorial induction.

## Finite Gibbs instance

`Common/Thermal/BlochDeDominicis/GibbsExpectation/Recursion.lean` constructs
`finiteGibbsExpectationRecursion`. This module is the finite implementation boundary. It discharges
the generic contract using:

- the canonical finite Gibbs density-state expectation;
- finite diagonal evolution and trace-ratio identities;
- KMS rotation and exchange-commutator hypotheses;
- the normalized two-point and peel formulas.

`Common/Thermal/BlochDeDominicis/Induction.lean` is the public finite specialization. Its proof is a
single application of the generic recursion theorem to `finiteGibbsExpectationRecursion`.

## Bosonic and completed-space boundary

A finite set of bosonic modes still has the infinite occupation type

```lean
Bosonic.Occupation Mode := Mode →₀ ℕ
```

Therefore no `[Fintype (Bosonic.Occupation Mode)]` shortcut is permitted.

Issue #421 provides the implementation-independent pairing contract but does not claim a bosonic
thermal-state instance. That work belongs to:

- #435 for a convergence-aware bosonic Gibbs/KMS and perturbative vertical slice;
- #440 for completed Fock representations, trace-class Gibbs states, and unbounded-operator domains.

The first bosonic instance may be coefficientwise or summability-aware. It must expose every
summability, integrability, product-closure, and positivity assumption. Creation, annihilation, and
number operators must not be presented as bounded continuous operators unless boundedness has
actually been proved on the chosen representation.

## Dependency and CI guards

The intended dependency direction is:

```text
ExpectationRecursion
        ↑
finite Gibbs recursion instance
        ↑
finite public Bloch–de Dominicis theorem
```

The generic recursion module must not import or mention finite Gibbs, density operators, traces,
diagonal evolution, algebraic Fock space, occupation-basis formulas, or finite-configuration
assumptions.

`scripts/check_bloch_de_dominicis_expectation_boundary.py` enforces this boundary in CI. The broader
SecondQuantization architecture and removed-identifier scripts additionally prevent statistics
inversion, deleted compatibility paths, and retired functional wrappers from returning.

## Status of issue #421

The following packages are complete:

- canonical density-operator expectation and finite Hilbert-Fock realization;
- destructive fermionic migration to density-state expectations;
- separation of generic diagonal traces, finite weighted sums, and occupation-basis bridges;
- trace-ratio ownership for normalized finite Bloch–de Dominicis proofs;
- generic `ExpectationPairingRecursion` and finite Gibbs instance;
- architecture guards for removed APIs and the generic expectation boundary.

Remaining work under #421 is documentation/final repository validation and any deliberately selected
finite free-fermion entropy corollaries. A genuine bosonic Gibbs/KMS implementation and completed
unbounded-operator theory remain separate research tracks under #435 and #440.
