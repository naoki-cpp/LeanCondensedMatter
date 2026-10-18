# Thermal expectation and Bloch--de Dominicis architecture

## Canonical expectation

For bounded observables, the physical normalized expectation is

```lean
QuantumTheory.DensityOperator.expectation
    (ρ : QuantumTheory.DensityOperator H) : (H →L[ℂ] H) →L[ℂ] ℂ.
```

Finite-dimensional trace and occupation-basis formulas are representations of this same expectation,
not alternative state models.

For a finite configuration type, `Common/Algebra/FiniteHilbertOperator.lean` owns the finite Hilbert
basis and transport of algebraic Fock endomorphisms to bounded operators. The thermal state is the
generic pure-point Gibbs density operator from `QuantumTheory.Gibbs.Eigenbasis`; the finite
SecondQuantization layer only supplies the representation-specific adapter.

The finite Gibbs expectation satisfies the usual trace-ratio formula

```text
Tr[e^{-βH₀} A] / Tr[e^{-βH₀}].
```

## Coordinate infrastructure

The reusable finite coordinate layer is split by responsibility:

| Owner | Responsibility |
|---|---|
| `QuantumTheory/Gibbs/Eigenbasis.lean` | Boltzmann weights, partition functions, probabilities, pure-point Gibbs states. |
| `Common/Algebra/FiniteHilbertOperator.lean` | Finite Hilbert realization and algebraic-operator transport. |
| `Common/Thermal/FiniteGibbsExpectationBridge.lean` | Canonical finite density-state expectation adapter and pure-point probability formula. |
| `Common/Thermal/FiniteGibbsCoordinate.lean` | Complex Boltzmann weights, diagonal-evolution traces, and trace-ratio formulas. |
| `Common/Algebra/DiagonalTrace.lean` | Summability-aware diagonal trace infrastructure. |
| `Common/Algebra/FiniteTrace.lean` | Canonical finite algebraic Fock trace and unnormalized scalar weight sums. |
| `Common/Thermal/BlochDeDominicis/NormalizedTwoPointTrace.lean` | Statistics-independent normalized two-point diagonal trace identity with explicit summability and nonzero denominators. |
| `Common/Thermal/BlochDeDominicis/GibbsExpectation/` | Finite density-state specializations: two-point, peel, four-point, and recursion formulas. |

Raw `weightSum` formulas are scalar coordinate infrastructure, not normalized-state models. The finite Gibbs expectation retains the canonical pure-point density state as its physical
meaning. For finite fermionic mode types,
`freePartitionFunction_eq_coe_eigenbasisPartitionFunction` identifies the complex finite-coordinate
partition function with the canonical real pure-point partition function after coercion to `ℂ`.

## Generic pairing recursion

`Common/Thermal/BlochDeDominicis/ExpectationRecursion.lean` owns

```lean
ExpectationPairingRecursion Operator s
```

with only the ordered expectation, pair values, admissibility, empty normalization, pair-deletion
stability, and KMS/exchange first-pair recurrence. The theorem
`ExpectationPairingRecursion.bloch_de_dominicis` derives the full pairing expansion.

The generic recursion has no occupation basis, trace implementation, density-state construction, or
finite-dimensional assumption. Its `admissible` predicate is where analytic obligations such as
summability, integrability, domain closure, and KMS hypotheses enter.

## Fermionic implementations

The finite Gibbs implementation specializes the generic recursion using the finite pure-point Gibbs
state, imaginary-time evolution, trace-ratio identity, and KMS/exchange relations. The finite
density-state specialization depends directly on `fermionEnergy` and the generic pure-point state;
finite complex Boltzmann coordinates are a separate proof/perturbation lane.

`Fermionic.Thermal.FreeEntropy` derives the finite occupation marginal from the canonical
number-operator expectation. The mean energy then uses this marginal, while the binary-entropy
formula specializes the generic pure-point Gibbs entropy identity. These are thermodynamic
consequences of the same density state, not a separate probability-state construction.

`Fermionic.Thermal.BoltzmannSummability` owns the representation-independent theorem that
one-particle Gibbs summability implies summability over fermionic occupation configurations.

The completed free-fermion implementation lives under `Fermionic.Thermal.Completed`.
`completedFreeGibbsDensityOperator` is the representation-specific name for the generic pure-point
Gibbs state on the completed occupation Hilbert basis. Bounded completed ladder operators then provide
KMS, first-pair/peel, and pairing-recursion results without introducing a finite-mode assumption into
the generic recursion.

Unbounded observables do not use `DensityOperator.expectation`. The completed total-number operator
is owned by `Fermionic.CompletedSpace.Diagonal`, while
`Fermionic.Thermal.Completed.TotalNumberExpectation` defines its explicit Gibbs-integrability
condition and spectral expectation. Potentially unbounded energy expectation remains generic in
`QuantumTheory.Gibbs.EigenbasisExpectation`; there is no public arbitrary-diagonal thermal
expectation API.

Bosonic two-field occupation-diagonal coefficients are algebraic imaginary-time facts, owned by
`Bosonic/ImaginaryTime/ImaginaryTimeEvolution.lean`. The single mode-indexed theorem
`diagonalCoeff_evolve_annihilate_comp_create` uses `Common.diagonalCoeff` directly; its equal-mode
and distinct-mode cases do not require Gibbs summability or temperature assumptions.

## Bosonic boundary

Even for finite `Mode`,

```lean
Bosonic.Occupation Mode := Mode →₀ ℕ
```

is infinite. `Bosonic/Thermal/ConvergenceAwareGibbs.lean` therefore defines a normalized functional
on an explicit summability domain rather than pretending that finite-configuration traces apply.
The linear expectation is defined on the summable-operator submodule; additivity retains explicit summability hypotheses.

`Bosonic/Thermal/FreeThermalField.lean` owns the free thermal field labels, ordered algebraic-Fock
products, and normalized pair kernel independently of pairing recursion. KMS, product summability,
and the kernel's equality to Gibbs two-field expectations consume these data directly.
`Bosonic/Thermal/BlochDeDominicis/ConcreteExpectationRecursion.lean` constructs the Common
recursion directly with `freeGibbsExpectation`. Under explicit positive one-mode Boltzmann
exponents, `FreeThermalField.freeGibbsSummable_orderedProduct` proves summability of every finite
field product, including every remaining product after pair deletion. The first-pair recurrence
uses those analytic results before the representation-independent pairing induction is applied.
No additional zero-totalization of the domain expectation is needed.

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

- extend the established free-field product summability and KMS/exchange recurrence to further
  operator families with explicit domain conditions;
- establish a justified bosonic operator-integration boundary;
- build completed bosonic Fock/operator-domain theory;
- extend connected expansions from the proved fermionic two-point case to higher/source insertions;
- formulate infinite-mode and thermodynamic-limit results with explicit analytic hypotheses.

## Scalar exchange expansion

The finite position-indexed expansion of a recursive exchange sum is owned by
`Analysis/ScalarExchange/Peel.lean`. `ScalarExchange.peelSum_eq_sum` applies to labelled
factors; `ScalarExchange.peelSumWithCoefficients_eq_sum` applies to factors paired with their
scalar coefficients. Both preserve the ordered product after deleting one position and accept
an arbitrary complex exchange factor. Common finite Gibbs, bosonic free Gibbs, and completed
fermionic Gibbs proofs use these algebraic identities directly. CCR/CAR relations, KMS rotation,
trace identities, and summability remain in the respective thermal implementations.
The same module owns the field identity that solves the scalar equations left by exchange and
rotation. Bosonic and completed fermionic first-pair reductions apply it with remainder coefficients
`1` and `-1` respectively. Their KMS proofs, denominator nonvanishing, and fermionic odd-tail
sign proof remain in the representation-specific consumers. The algebraic identity assumes only
a field and the two scalar equalities, and introduces no thermal-state contract.

`Common/Thermal/BlochDeDominicis/NormalizedTwoPointTrace.lean` applies the general trace peel
theorem to a singleton coefficient-paired tail. Its
`normalizedTsumTrace_comp_eq_div_of_zetaCommutator` accepts an arbitrary configuration type;
finite types are included without a countability assumption. Partition-diagonal summability,
rotated double-series summability, and nonzero partition and exchange denominators remain explicit.
The singleton peel's diagonal summability follows by multiplying the partition diagonal series
by the exchange coefficient.

The finite Gibbs two-point theorem supplies automatic finite summability and the canonical
density-state trace bridge. `Bosonic/Thermal/BlochDeDominicis/ConcreteMixedTwoPoint.lean`
consumes the same common theorem with occupation-space summability and denominator proofs;
`TwoPoint.lean` owns the supporting analytic estimates. Neither consumer defines another normalized
state. This shared trace identity does not imply closure of arbitrary summable operators under
composition.

## Exponential denominators

`Analysis/Exponential.lean` owns `Complex.exp_ne_one_of_re_ne_zero`: a complex exponential
is different from one when its exponent has nonzero real part. The bosonic Bose and KMS denominator
proofs use this fact directly, supplying positivity or negativity of the exponent from their
explicit positive Boltzmann-exponent hypothesis. No representation-specific denominator theorem
is needed.

Mathlib's `Complex.norm_exp` and `Real.exp_eq_one_iff` provide the norm and real-exponential steps.
The shared theorem combines those existing results; it does not require a classification of complex
exponential periods.
