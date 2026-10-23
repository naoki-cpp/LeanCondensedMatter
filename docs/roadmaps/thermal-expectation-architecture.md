# Thermal expectation and Bloch--de Dominicis architecture

## State-independent expectation boundary

For bounded observables, the physical normalized expectation is

```lean
QuantumTheory.DensityOperator.expectation
    (ρ : QuantumTheory.DensityOperator H) : (H →L[ℂ] H) →L[ℂ] ℂ.
```

Finite-dimensional trace and occupation-basis formulas are representations of this same expectation,
not alternative state models. Here *canonical* in a declaration's documentation can mean the
preferred representation/API; it must not be interpreted as a fixed-particle-number canonical
ensemble. A density operator and its expectation do not prescribe any particle-number ensemble.

For a finite configuration type, `Common/Algebra/FiniteHilbertOperator.lean` owns the finite Hilbert
basis and transport of algebraic Fock endomorphisms to bounded operators. The thermal state is the
generic pure-point Gibbs density operator from `QuantumTheory.Gibbs.Eigenbasis`; the finite
SecondQuantization layer only supplies the representation-specific adapter.

The finite Gibbs expectation satisfies the usual trace-ratio formula

```text
Tr[e^{-βH₀} A] / Tr[e^{-βH₀}].
```

## Coordinate infrastructure

Finite density-state expectations are finite-index instances of
`DensityOperator.expectation_eq_tsum_diagonal`. Completed-space bounded-operator expectations
use the same dimension-independent diagonal formula; summability comes from the Gibbs
density state's trace-class condition. Finite algebraic operators still require the
finite-dimensional transport to bounded operators.

The reusable finite coordinate layer is split by responsibility:

| Owner | Responsibility |
|---|---|
| `QuantumTheory/Gibbs/Boltzmann.lean` | Real Boltzmann weights, partition functions, normalized probabilities, and summability. |
| `QuantumTheory/Gibbs/Eigenbasis.lean` | Gibbs density states built from energy eigenbases and scalar Boltzmann data. |
| `Common/Algebra/FiniteHilbertOperator.lean` | Finite Hilbert realization and algebraic-operator transport. |
| `Common/Thermal/FiniteGibbsExpectationBridge.lean` | Canonical finite density-state expectation adapter and pure-point probability formula. |
| `Common/Thermal/FiniteGibbsCoordinate.lean` | Complex Boltzmann weights, diagonal-evolution traces, and trace-ratio formulas. |
| `Common/Algebra/DiagonalTrace.lean` | Summability-aware diagonal trace infrastructure. |
| `Common/Algebra/FiniteTrace.lean` | Canonical finite algebraic Fock trace and unnormalized scalar weight sums. |
| `Common/Thermal/BlochDeDominicis/NormalizedTwoPointTrace.lean` | Statistics-independent normalized two-point diagonal trace identity with explicit summability and nonzero denominators. |
| `Common/Thermal/BlochDeDominicis/GibbsExpectation/` | Finite Gibbs-state specializations: two-point, peel, four-point, recursion, and its finite Gibbs pairing theorem. |

Raw `weightSum` formulas are scalar coordinate infrastructure, not normalized-state models. The finite Gibbs expectation retains the canonical pure-point density state as its physical
meaning. For finite fermionic mode types,
`freePartitionFunction_eq_coe_eigenbasisPartitionFunction` identifies the complex finite-coordinate
partition function with the canonical real pure-point partition function after coercion to `ℂ`.

## Canonical and grand-canonical conditioning

`Common/Thermal/GrandCanonicalSectorDecomposition.lean` owns the scalar bridge:
restricting grand-canonical Boltzmann weights to sharp-number sectors gives
the canonical weights multiplied by `exp (β μ N)`. Global Gibbs summability
implies summability in every sector, without a finite occupation-basis hypothesis.
For a nonempty sector the probability is `p_N = exp (β μ N) Z_N / Ξ > 0`;
empty sectors contribute zero without a normalized canonical density.

The same module uses sigma-fiber reindexing to prove
`Ξ = ∑_N exp (β μ N) Z_N` and `∑_N p_N = 1`.
`Common/Thermal/CanonicalGrandCanonicalCompatibility.lean` uses this scalar
data to prove the completed-Fock bounded-operator identity
`P_N ρ_GC P_N = p_N ρ_{N,full}`, where `ρ_{N,full}` is the existing
isometric zero extension of the canonical density. The left-hand side
is an unnormalized positive operator, not itself a density state.

General bounded-observable expectation and full density-operator decompositions
remain separate tasks.

## Generic pairing recursion

`Common/Thermal/BlochDeDominicis/ExpectationRecursion.lean` owns

```lean
ExpectationPairingRecursion Operator s
```

with only the ordered expectation, pair values, admissibility, empty normalization, pair-deletion
stability, and an assumed first-pair recurrence. The theorem
`ExpectationPairingRecursion.bloch_de_dominicis` derives the full pairing expansion.

The generic recursion has no occupation basis, trace implementation, density-state construction,
finite-dimensional assumption, or ensemble choice. Its `admissible` predicate is where analytic
obligations such as summability, integrability, domain closure, and KMS hypotheses enter. It does
not assert that an arbitrary fixed-`N` state is Gaussian: the pairing theorem applies only after
its first-pair recurrence is proved for the specific state.

The generic induction remains in `ExpectationRecursion.lean`. The concrete finite Gibbs
specialization `finiteGibbsExpectation_prod_eq_sum_pairing` is colocated with its implementing
`finiteGibbsExpectationRecursion` in `GibbsExpectation/Recursion.lean`. Both are formulated in
terms of an arbitrary energy function on configurations; the Gibbs implementation does not decide
whether those configurations represent a fixed-`N` sector or the full Fock space.

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
It uses `Common.grandCanonicalGibbsDensityOperator (Config := Fermionic.Occupation Mode) ε β μ`
without an additional zero-chemical-potential fermionic density constructor. Its completed CAR
intertwining and KMS factors use the effective thermal dispersion `ε i - μ`. The first-pair/peel
and Wick pairing recursion are instantiated for this explicit grand-canonical state, with no
finite-mode assumption introduced into the generic recursion. Fermionic KMS factors are
exponentials of real energies, so `1 + g` is automatically nonzero; the completed fermionic
pairing-recursion adapter consequently uses `admissible := True`. The Gibbs state still requires
summability over occupation configurations. In the separate finite-mode bridge,
`completedGrandCanonicalGibbs_intertwines_finite` transports the density state to the finite Hilbert
realization; `finiteGrandCanonicalGibbsExpectation_eq_diagonalTraceRatio` then applies the common
algebraic summable-trace ratio from #4074.

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

is infinite. `Bosonic/Thermal/ConvergenceAwareGibbs.lean` therefore defines a grand-canonical normalized functional parameterized by explicit `ε`, `β`,
and `μ` on a summability domain, rather than pretending that finite-configuration traces apply.
The linear expectation is defined on the summable-operator submodule; additivity retains explicit summability hypotheses. The shared effective-energy transport uses `ξ i = ε i - μ`; physical Dyson evolution continues to use `ε`.

`Bosonic/Thermal/FreeThermalField.lean` owns the free thermal field labels, ordered algebraic-Fock
products, and normalized pair kernel independently of pairing recursion. KMS, product summability,
and the kernel's equality to Gibbs two-field expectations consume these data directly.
`Bosonic/Thermal/BlochDeDominicis/ConcreteExpectationRecursion.lean` applies the
Common pairing recursion at the effective thermal energy `ξ i = ε i - μ` and exposes
`grandCanonicalGibbsExpectation_eq_sum_pairing_concrete` for explicit chemical potential `μ`.
Under `0 < β * (ε i - μ)`, finite ordered free-field products have summable Gibbs numerators,
including products after pair deletion. The first-pair recurrence and KMS rotation supply the
analytic hypotheses before the representation-independent pairing induction. This grand-canonical
Wick conclusion does not extend automatically to a sharp-particle-number canonical state.

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

## Ensemble-parameter dependency audit

The following is the boundary for issue
[#3986](https://github.com/naoki-cpp/LeanCondensedMatter/issues/3986), after the
ensemble-neutral refactors #3988, #3991, #3993, #3996, #3997, #3999, #4002, #4004, and #4008.
An API being *statistics-independent* does not by itself make a Gibbs expectation or trace
independent of the ensemble: the operator algebra and the chosen state are separate inputs.

| Layer | Existing owner | Ensemble dependence |
|---|---|---|
| Algebraic operator products, imaginary-time Dyson coefficients, coefficientwise integration | `Common.Perturbation.DysonExpansion`, `Common.Perturbation.FiniteOperatorIntegral` | No Gibbs state, fixed particle number, or chemical potential is assumed. |
| Formal series normalization and connected/moment/cumulant combinatorics | `Analysis.PowerSeries.Normalization`, `Analysis.PowerSeries.Moment`, `Combinatorics.Cumulant` | Purely algebraic; state-dependent moment identities are *inputs* to the connected-diagram proof. |
| Normalized two-point subtraction and composite-current field expansions | `QuantumTheory.LinearResponse.connectedCorrelation`, `Fermionic.Transport.CurrentInsertions` | The subtraction and finite-sum expansion do not require Gibbs; physical second-cumulant interpretation requires normalization. |
| Abstract thermal pairing induction | `Common.Thermal.BlochDeDominicis.ExpectationRecursion` | The induction is generic, but each concrete state must prove its first-pair recurrence; fixed-`N` Wick factorization is **not** automatic. |
| Finite trace ratios and normalized Dyson trace-series coefficients | `Common.Thermal.FiniteGibbsCoordinate`, `Common.Perturbation.DysonTraceSeries` | Concrete Gibbs specialization on the supplied finite configuration type. That type may be a selected sector or all configurations; the trace ratio alone does not select an ensemble. |
| Completed / infinite-occupation Gibbs realizations | `QuantumTheory.Gibbs.Eigenbasis`, `Bosonic.Thermal.ConvergenceAwareGibbs` | Density states require summable weights; unbounded bosonic algebraic observables also require an explicit summability domain with `μ` in the thermal weight. |

**Migration policy.** Introduce a sharp `N` or chemical potential `μ` only in the
appropriate physical state constructors and their genuinely ensemble-dependent expectations.
Do not thread either parameter through formal Dyson coefficients, generic pairing
combinatorics, abstract connected correlations, or cumulant inversion. The grand-canonical
KMS evolution uses `H - μ N̂` on its specified observable algebra; fixed-`N` states require
a separate analysis of the number-preserving algebra and higher cumulants. A finite-mode
bosonic Fock occupation type is still infinite, so a finite-configuration theorem never
justifies omitting its summability hypotheses.

This audit records **module ownership**, not completion of the fixed-`N` or `μ`-dependent
state construction. Those constructions, their full consumer migration, and their physical
verification remain open in #3986.

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

`Common/Thermal/BlochDeDominicis/ExpectationRecursion.lean` also owns
`indexedPeel_sum_eq_firstPair`: it distributes the scalar KMS ratio through a finite indexed
peel, reindexes each erased tail, and replaces bare exchange coefficients by normalized
contractions. Both completed fermionic and free bosonic first-pair adapters use this same
sum conversion; their exchange/KMS and analytic conditions remain representation-specific.

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
