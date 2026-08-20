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

for a finite configuration type. `Common/Thermal/FiniteHilbertOperator.lean` owns the Hilbert basis,
algebraic-to-Hilbert equivalence, and transport of algebraic-Fock endomorphisms to bounded operators.
The normalized thermal state is not reimplemented in SecondQuantization: it is

```lean
QuantumTheory.finitePurePointGibbsDensityOperator finiteHilbertBasis energy β
```

and `finiteGibbsExpectation` is its expectation after the algebraic operator transport.

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
| Generic pure-point Gibbs state | `QuantumTheory/Gibbs/PurePoint.lean` | Boltzmann weights, partition function, normalized probabilities, and finite/countable pure-point density states. |
| Finite Hilbert transport | `Common/Thermal/FiniteHilbertOperator.lean` | Finite Hilbert basis and transport of algebraic Fock operators to bounded operators. |
| Generic diagonal trace | `Common/Thermal/DiagonalTrace.lean` | Matrix coefficients, extensionality, composition, and summability-aware `tsumTrace`. |
| Finite unnormalized sums | `Common/Thermal/FiniteWeightedTrace.lean` | Finite trace, weighted trace, and total weight. |
| Normalized coordinate functional | `Common/Thermal/WeightedDiagonalFunctional.lean` | `normalizedWeightedDiagonal` for an arbitrary finite complex weight. |
| Density-state coordinate formulas | `Common/Thermal/FiniteGibbsExpectationBridge.lean` and `Common/Thermal/BlochDeDominicis/GibbsExpectation/Core.lean` | Algebraic-operator expectation adapter, diagonal-sum and operator-integral formulas, plus the derived trace-ratio and normalized Boltzmann-weighted coordinate identities. |

`normalizedWeightedDiagonal` has no physical interpretation for an arbitrary complex weight. It is
called a Gibbs expectation only after specialization to positive Boltzmann weights. The corresponding
comparison with the canonical density-state expectation is derived directly in the finite Gibbs
expectation core; there is no separate compatibility module.

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

- the generic finite pure-point Gibbs density state through `finiteGibbsExpectation`;
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

## Bosonic convergence-aware functional slice

`Bosonic/Thermal/ConvergenceAwareGibbs.lean` defines

```lean
ConvergenceAwareGibbsFunctional Observable
```

as a linear expectation on an explicit `Submodule` of analytically admissible observables, together
with a distinguished unit and normalization.  For algebraic bosonic Fock space, the concrete domain
is

```lean
freeGibbsDomain ε β
```

whose membership condition is summability of the diagonal coefficients of `e^{-βH₀} A`.  Under
`∀ i, 0 < β * ε i`, `freeGibbsFunctional ε β` supplies the canonical normalized free functional.
This is an algebraic, matrix-coefficient realization; it does not promote ladder operators to
bounded operators or claim a completed trace-class state.

`Bosonic/Thermal/BlochDeDominicis/ExpectationRecursion.lean` defines

```lean
ConvergenceAwarePairingRecursion Observable Operator s
```

which records ordered-product domain membership, pair-deletion stability, and the KMS/exchange
first-pair recurrence.  Its adapter `toExpectationPairingRecursion` reuses the Common pairing theorem.
The remaining bosonic work is to discharge these hypotheses for useful ladder-operator families and
the products generated by the first Dyson orders.

## Dependency direction

```text
ExpectationRecursion
        ↑
concrete expectation/KMS instance
        ↑
public Bloch–de Dominicis theorem
```

The generic recursion must remain independent of finite Gibbs adapters and coordinate formulas.
`scripts/check_bloch_de_dominicis_expectation_boundary.py` enforces this boundary. The
SecondQuantization architecture checks additionally reject removed compatibility modules and invalid
dependency directions.

## Open work

- Prove the bosonic KMS/exchange first-pair recurrence on explicit summable operator families.
- Establish product closure for the first nontrivial Dyson/Wick orders.
- Replace finite-output-basis operator integration by a justified bosonic integration boundary.
- Completed Fock-space representations and unbounded operator domains.
- Correlation-function expansions with external legs.
- Infinite-mode and thermodynamic-limit statements with explicit analytic hypotheses.
