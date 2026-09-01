# Thermal expectation and Bloch--de Dominicis architecture

## Canonical expectation

For bounded observables, the physical normalized expectation is

```lean
QuantumTheory.DensityOperator.expectation
    (ρ : QuantumTheory.DensityOperator H) : (H →L[ℂ] H) →L[ℂ] ℂ.
```

Finite-dimensional trace and occupation-basis formulas are representations of this same expectation,
not alternative state models.

For a finite configuration type, `Common/Thermal/FiniteHilbertOperator.lean` owns the finite Hilbert
basis and transport of algebraic Fock endomorphisms to bounded operators. The thermal state is the
generic pure-point Gibbs density operator from `QuantumTheory.Gibbs.PurePoint`; the finite
SecondQuantization layer only supplies the representation-specific adapter.

The finite Gibbs expectation satisfies the usual trace-ratio formula

```text
Tr[e^{-βH₀} A] / Tr[e^{-βH₀}].
```

## Coordinate infrastructure

The reusable finite coordinate layer is split by responsibility:

| Owner | Responsibility |
|---|---|
| `QuantumTheory/Gibbs/PurePoint.lean` | Boltzmann weights, partition functions, probabilities, pure-point Gibbs states. |
| `Common/Thermal/FiniteHilbertOperator.lean` | Finite Hilbert realization and algebraic-operator transport. |
| `Common/Thermal/DiagonalTrace.lean` | Summability-aware diagonal trace infrastructure. |
| `Common/Thermal/FiniteWeightedTrace.lean` | Finite unnormalized weighted sums. |
| `Common/Thermal/WeightedDiagonalFunctional.lean` | Generic normalized finite coordinate functional. |
| `Common/Thermal/BlochDeDominicis/GibbsExpectation/` | Density-state coordinate, trace-ratio, and finite Gibbs formulas. |

A generic complex-weight coordinate functional acquires a Gibbs interpretation only after
specialization to physical Boltzmann weights.

## Generic pairing recursion

`Common/Thermal/BlochDeDominicis/ExpectationRecursion.lean` owns

```lean
ExpectationPairingRecursion Operator s
```

with only the ordered expectation, pair values, admissibility, empty normalization, pair-deletion
stability, and KMS/exchange first-pair recurrence. The theorem
`ExpectationPairingRecursion.expectation_eq_sum_pairing` derives the full pairing expansion.

The generic recursion has no occupation basis, trace implementation, density-state construction, or
finite-dimensional assumption. Its `admissible` predicate is where analytic obligations such as
summability, integrability, domain closure, and KMS hypotheses enter.

## Fermionic implementations

The finite Gibbs implementation specializes the generic recursion using the finite pure-point Gibbs
state, imaginary-time evolution, trace-ratio identity, and KMS/exchange relations.

The completed free-fermion implementation lives under `Fermionic.Thermal.Completed`. It uses bounded
completed ladder operators and a summability-controlled pure-point Gibbs state to provide KMS,
first-pair/peel, and pairing-recursion results without introducing a finite-mode assumption into the
generic recursion.

## Bosonic boundary

Even for finite `Mode`,

```lean
Bosonic.Occupation Mode := Mode →₀ ℕ
```

is infinite. `Bosonic/Thermal/ConvergenceAwareGibbs.lean` therefore defines a normalized functional
on an explicit summability domain rather than pretending that finite-configuration traces apply.
`ConvergenceAwarePairingRecursion` records the corresponding domain and pair-deletion/KMS
obligations and adapts them to the Common pairing theorem.

## Dependency boundary

```text
ExpectationRecursion
        ↑
representation-specific expectation/KMS data
        ↑
public Bloch--de Dominicis theorem.
```

The generic recursion must remain independent of finite-coordinate or representation-specific Gibbs
implementations.

## Open work

- discharge the bosonic KMS/exchange recurrence on useful summable operator families;
- prove bosonic product-domain closure and a justified operator-integration boundary;
- build completed bosonic Fock/operator-domain theory;
- extend connected expansions from the proved fermionic two-point case to higher/source insertions;
- formulate infinite-mode and thermodynamic-limit results with explicit analytic hypotheses.
