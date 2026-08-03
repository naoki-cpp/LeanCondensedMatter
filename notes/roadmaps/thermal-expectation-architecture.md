# Thermal expectation and Bloch–de Dominicis architecture

This document is the source of truth for normalized thermal expectations, finite coordinate
formulas, and the generic Bloch–de Dominicis pairing recursion.

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

## Generic pairing recursion

`Common/Thermal/BlochDeDominicis/ExpectationRecursion.lean` owns

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

`ExpectationPairingRecursion.expectation_eq_sum_pairing` derives the complete pairing expansion. The
module has no configuration type, no occupation basis, no trace implementation, no density-state
construction, and no finite-dimensional assumption.

The `admissible` predicate is the extension point for analytic obligations such as summability,
integrability, domain closure, and KMS hypotheses.

## Finite Gibbs instance

`Common/Thermal/BlochDeDominicis/GibbsExpectation/Recursion.lean` constructs the finite Gibbs
instance. It combines:

- the canonical finite Gibbs density-state expectation;
- finite diagonal imaginary-time evolution;
- the trace-ratio formula;
- KMS rotation and exchange identities;
- normalized two-point and pair-deletion formulas.

`Common/Thermal/BlochDeDominicis/Induction.lean` exposes the finite theorem by applying the generic
recursion theorem to this instance.

## Bosonic boundary

For finite `Mode`, the bosonic occupation type

```lean
Bosonic.Occupation Mode := Mode →₀ ℕ
```

is still infinite. A bosonic thermal instance cannot use finite-configuration sums without proving
summability.

A completed bosonic implementation must state:

- convergence of the partition function and relevant moments;
- integrability and interchange-of-sum conditions;
- stability of operator products on the chosen domain;
- KMS and positivity hypotheses;
- boundedness, closability, or self-adjointness facts appropriate to the representation.

## Dependency direction

```text
ExpectationRecursion
        ↑
concrete expectation/KMS instance
        ↑
public Bloch–de Dominicis theorem
```

The generic recursion must remain independent of finite Gibbs implementations and coordinate
formulas. `scripts/check_bloch_de_dominicis_expectation_boundary.py` enforces this boundary. The
SecondQuantization architecture checks additionally reject removed compatibility modules and invalid
dependency directions.

## Open work

- A convergence-aware bosonic Gibbs/KMS instance.
- Completed Fock-space representations and unbounded operator domains.
- Correlation-function expansions with external legs.
- Infinite-mode and thermodynamic-limit statements with explicit analytic hypotheses.
