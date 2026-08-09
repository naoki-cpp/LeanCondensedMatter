# Thermal expectation and Bloch–de Dominicis architecture

This document is the source of truth for normalized thermal expectations, finite coordinate
formulas, number-conserving matrix evaluation, and the remaining generic pairing recursion used at
genuinely non-bipartite or diagrammatic boundaries.

## Canonical normalized expectation

The physical normalized expectation is

```lean
QuantumTheory.DensityOperator.expectation
    (ρ : QuantumTheory.DensityOperator H) : (H →L[ℂ] H) →L[ℂ] ℂ
```

It supplies linearity, normalization, contractivity, positivity, and reality results for bounded
operators. Finite-dimensional trace and diagonal formulas are theorems about this same expectation.

Finite SecondQuantization uses

```lean
FiniteHilbertFock Config := EuclideanSpace ℂ Config
```

for a finite configuration type. Algebraic-Fock endomorphisms are transported to bounded operators
on this Hilbert realization. `finiteGibbsDensityOperator` is the normalized state and
`finiteGibbsExpectation` is its expectation after transport.

## Finite trace-ratio formula

For finite configurations, the canonical expectation is proved equal to

```text
Tr[e^{-βH₀} A] / Tr[e^{-βH₀}]
```

through `finiteGibbsExpectation_eq_trace_div` in the finite Gibbs Bloch–de Dominicis layer. This
trace-ratio identity is the physical finite-state formula used by normalized thermal proofs.

## Coordinate proof infrastructure

Explicit occupation-basis sums remain available when the finite coordinate formula is itself useful.
They are not alternative state models.

| Layer | Module | Responsibility |
|---|---|---|
| Generic diagonal trace | `Common/Thermal/DiagonalTrace.lean` | Matrix coefficients, extensionality, composition, and summability-aware `tsumTrace`. |
| Finite unnormalized sums | `Common/Thermal/FiniteWeightedTrace.lean` | Finite trace, weighted trace, and total weight. |
| Normalized coordinate functional | `Common/Thermal/WeightedDiagonalFunctional.lean` | `normalizedWeightedDiagonal` for an arbitrary finite complex weight. |
| Gibbs occupation-basis comparison | `Common/Thermal/FiniteGibbsOccupationBasisBridge.lean` | Equality between the canonical finite Gibbs expectation and the normalized Boltzmann-weighted sum. |
| Density-state coordinate formula | `Common/Thermal/FiniteGibbsExpectationBridge.lean` | Diagonal-sum and operator-integral formulas for the canonical finite Gibbs expectation. |

`normalizedWeightedDiagonal` has no physical interpretation for an arbitrary complex weight. It is
called a Gibbs expectation only after specialization to positive Boltzmann weights and proof of the
density-state comparison.

## Number-conserving matrix backend

For a number-conserving free Gaussian state, creator–creator and annihilator–annihilator contractions
vanish. After separating the two operator families, the surviving matchings are bipartite and are
indexed by permutations rather than arbitrary perfect pairings.

`Common/Thermal/BlochDeDominicis/MatrixEvaluation.lean` is the canonical backend for this sector. It
provides

```lean
bipartitePairMatrix

determinantBipartitePairValue
permanentBipartitePairValue
```

and the first-row recurrences needed to identify a thermal moment recurrence with Mathlib's
`Matrix.det` or `Matrix.permanent`.

The intended rule is:

- free fermionic number-conserving moments use a determinant, together with any fixed sign imposed by
  the chosen external operator-order convention;
- free bosonic number-conserving moments use a permanent;
- explicit `Pairing` enumeration is not a second thermal evaluation backend for this sector.

This reduces the combinatorial state carried by the thermal layer from all perfect pairings to the
matrix invariant that already represents the surviving permutation sum.

## Generic pairing recursion

`Common/Thermal/BlochDeDominicis/ExpectationRecursion.lean` still owns

```lean
ExpectationPairingRecursion Operator s
```

The contract contains only:

- expectation of an ordered operator list;
- normalized pair values;
- an admissibility predicate;
- normalization of the empty product;
- admissibility after deleting a pair;
- the KMS/exchange first-pair recurrence.

`ExpectationPairingRecursion.expectation_eq_sum_pairing` derives the complete weighted perfect-pairing
expansion. This is now a deliberately more general interface than the number-conserving matrix
backend. It remains appropriate when explicit pairings themselves are needed by diagrammatics, and
for future Gaussian sectors with anomalous contractions before their Pfaffian/Hafnian backend is
introduced.

The module has no configuration type, no occupation basis, no trace implementation, no density-state
construction, and no finite-dimensional assumption. Its `admissible` predicate remains the extension
point for summability, integrability, domain closure, and KMS hypotheses.

## Finite Gibbs instance

`Common/Thermal/BlochDeDominicis/GibbsExpectation/Recursion.lean` constructs the finite Gibbs generic
recursion instance. It combines:

- the canonical finite Gibbs density-state expectation;
- finite diagonal imaginary-time evolution;
- the trace-ratio formula;
- KMS rotation and exchange identities;
- normalized two-point and pair-deletion formulas.

`Common/Thermal/BlochDeDominicis/Induction.lean` exposes the finite generic pairing theorem where the
fully general pairing representation is genuinely required.

## Bosonic boundary

For finite `Mode`, the bosonic occupation type

```lean
Bosonic.Occupation Mode := Mode →₀ ℕ
```

is still infinite. A bosonic thermal implementation cannot use finite-configuration sums without
proving summability.

A completed bosonic implementation must state:

- convergence of the partition function and relevant moments;
- integrability and interchange-of-sum conditions;
- stability of operator products on the chosen domain;
- KMS and positivity hypotheses;
- boundedness, closability, or self-adjointness facts appropriate to the representation.

## Bosonic convergence-aware functional and permanent endpoint

`Bosonic/Thermal/ConvergenceAwareGibbs.lean` defines

```lean
ConvergenceAwareGibbsFunctional Observable
```

as a linear expectation on an explicit `Submodule` of analytically admissible observables, together
with a distinguished unit and normalization. For algebraic bosonic Fock space, the concrete domain
is

```lean
freeGibbsDomain ε β
```

whose membership condition is summability of the diagonal coefficients of `e^{-βH₀} A`. Under
`∀ i, 0 < β * ε i`, `freeGibbsFunctional ε β` supplies the canonical normalized free functional.
This is an algebraic, matrix-coefficient realization; it does not promote ladder operators to
bounded operators or claim a completed trace-class state.

`Bosonic/Thermal/BlochDeDominicis/FreeExpectationRecursion.lean` now owns only the concrete thermal
field labels, ordered product, and pair kernel. The old boson-specific pairing-recursion adapter and
thermal pairing-sum endpoint are intentionally removed.

`Bosonic/Thermal/BlochDeDominicis/ConcreteExpectationRecursion.lean` derives the creator-first,
number-conserving first-row recurrence directly from CCR peel plus KMS rotation and proves that the
normal-ordered moment is the permanent of the creator–annihilator contraction matrix.

When an explicit `Pairing` is needed for graph connectivity or factorization,
`Bosonic/Diagrammatics/QuarticWickExpansion.lean` constructs the generic Common pairing contract at
the diagrammatic boundary instead of reintroducing a pairing-valued thermal API.

## Completed fermionic determinant endpoint

`Fermionic/CompletedSpace/ThermalRecursion.lean` is the completed-space number-conserving endpoint. It
derives the normal-ordered CAR/KMS recurrence and evaluates it with the common determinant backend.
The current creator-first ordering convention contributes a fixed normal-order sign multiplying the
determinant; this sign is an ordering convention, not a return to perfect-pairing enumeration.

Pairing-specific completed-thermal admissibility and pairing-sum endpoints are not part of this
number-conserving API.

## Dependency direction

The preferred number-conserving path is

```text
thermal KMS / operator peel
        ↓
bipartite normal-ordered recurrence
        ↓
MatrixEvaluation
        ↓
Matrix.det / Matrix.permanent
```

The general/diagrammatic path is separate:

```text
first-pair recurrence
        ↓
ExpectationPairingRecursion
        ↓
Pairing data used by diagrammatics
```

Do not route a number-conserving thermal evaluation through explicit perfect-pairing enumeration only
to collapse it back to a determinant or permanent. Conversely, do not erase `Pairing` from modules
whose statements require graph connectivity, crossings, components, or relabeling.

The generic recursion must remain independent of finite Gibbs implementations and coordinate
formulas. `scripts/check_bloch_de_dominicis_expectation_boundary.py` enforces this boundary. The
SecondQuantization architecture checks additionally reject removed compatibility modules and invalid
dependency directions.

## Open work

- Introduce Pfaffian/Hafnian backends for genuinely general Gaussian fermionic/bosonic expectations
  with anomalous contractions.
- Decide whether arbitrary balanced non-normal-ordered free-field families need a direct sorting
  bridge to the determinant/permanent endpoints, rather than going through a pairing theorem.
- Establish product closure for the first nontrivial Dyson/Wick orders.
- Replace finite-output-basis operator integration by a justified bosonic integration boundary.
- Completed bosonic Fock-space representations and unbounded operator domains.
- Correlation-function expansions with external legs.
- Infinite-mode and thermodynamic-limit statements with explicit analytic hypotheses.
