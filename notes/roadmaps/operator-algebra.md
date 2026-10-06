# Operator analysis (Track C)

Track C owns dimension-independent analytic infrastructure used by quantum theory, transport, and
second quantization.

## Fixed-sign commutator algebra

On the pinned Mathlib v4.33.1 (`0df444a360eaa60ab8c11dca51a86af692955474`), the ordinary
associative commutator is available through the Lie bracket,
`⁅A, B⁆ = A * B - B * A` (`LieRing.of_associative_ring_bracket`), with `Module.End` multiplication
identified with composition by `Module.End.mul_eq_comp`. The pinned API survey found no
`zetaCommutator`, q-commutator, or fixed-scalar twisted-commutator family matching
`A ∘ B - ζ • (B ∘ A)`.

Accordingly, `Analysis/ScalarExchange.lean` owns the representation-independent
`ScalarExchange.zetaCommutator` for associative complex algebras. The operator layer keeps the
ordinary commutator as a semantic `ζ = 1` endomorphism specialization, while second-quantization
code uses the generic bracket directly and selects `ζ` through `Statistics.zetaInt`. Re-check this
ownership after Mathlib upgrades.

## Infinite sums and spectral analysis

`Analysis/InfiniteSum/` provides reusable reindexing, fiberwise sum, and justified countable-sum
exchange tools.

`Analysis/Operator/Spectral/` provides compact self-adjoint spectral decomposition with countable
nonzero spectrum, finite multiplicities, eigenvector reconstruction, kernel completion, arbitrary
Hilbert-basis comparison, and positivity results.

These layers are physics-independent.

## Trace class

On the pinned Mathlib v4.34.1 revision `d13f23b723b8a846827a245b89c10fc7d3f11612`,
`CFC.abs T` is the canonical operator absolute value
`|T| = (T† T)^(1/2)`. The project therefore does not define a second operator-absolute-value
wrapper. General trace-class membership is based on summability of the nonnegative Hilbert-basis
diagonal of `CFC.abs T`.

Basis independence is reduced to the existing Hilbert--Schmidt layer: the diagonal term
`⟨eᵢ, |T| eᵢ⟩` equals `‖CFC.sqrt (CFC.abs T) eᵢ‖²`. Accordingly,
`ContinuousLinearMap.IsTraceClass T` is owned by Hilbert--Schmidt membership of
`CFC.sqrt (CFC.abs T)`, while `IsTraceClassWrt d T` is the equivalent diagonal criterion in a
chosen Hilbert basis. Basis choices remain witnesses rather than mathematical data stored in the
operator property.

`ContinuousLinearMap.SpectralTraceClass` is the self-adjoint specialization of the general
trace-class API: it stores `IsTraceClass T` and symmetry, while compactness is derived from general
trace-class compactness and spectral summability is derived from the compact self-adjoint
characterization. Its real-valued `spectralTrace` supplies eigenvalue-sum formulas, positivity,
and Hilbert-basis formulas; it does not define a second
bundled trace value. The neutral Hilbert-basis diagonal operator construction is owned by
`Analysis/Operator/Diagonal.lean`.

For `hT : IsTraceClass T`, `hT.traceNorm` is the basis-independent trace norm, defined from the
canonical squared Hilbert--Schmidt norm of `sqrt(|T|)`. Its Hilbert-basis diagonal formula is
exposed directly, without a second basis-relative trace-norm wrapper. The compact self-adjoint specialization identifies general trace-class membership with absolute
spectral summability and the general trace norm with the absolute eigenvalue sum. For positive bundled
spectral trace-class operators, that trace norm agrees with the spectral trace. The basis-independent
general complex trace is the absolutely convergent Hilbert-basis diagonal sum and agrees, on compact
self-adjoint operators, with the real spectral trace after coercion to `ℂ`.

## Hilbert--Schmidt operators

`Analysis/Operator/HilbertSchmidt/` provides basis-independent Hilbert--Schmidt membership, adjoint
invariance, closure under bounded composition, compactness, the canonical squared norm with direct
Hilbert-basis `Summable`/`HasSum` formulas, the pairing `innerHS`, and comparison with spectral trace
on the compact self-adjoint overlap.

General non-self-adjoint trace-class membership and its canonical trace norm are defined from the
Hilbert--Schmidt layer. `TraceClass/Factorization/Basic.lean` owns the trace-norm-independent
characterization `T = A† B` with Hilbert--Schmidt factors. `TraceClass/Factorization/Norm.lean`
adds the estimate `‖T‖₁ ≤ (‖A‖²_HS + ‖B‖²_HS) / 2` and a factorization satisfying
`‖A‖²_HS = ‖B‖²_HS = ‖T‖₁`. Compactness and trace convergence consume only the basic layer;
trace-norm estimates consume the norm-aware layer. `TraceClass/Ops/Basic.lean` owns membership closure
under addition, scalar multiplication, adjoint, and bounded left/right multiplication together with
complex-trace linearity; `TraceClass/Ops/Norm.lean` owns the corresponding trace-norm identities and
inequalities. In particular, every trace-class operator is compact without depending on the trace-value
implementation. The trace norm is adjoint-invariant and contractive under left/right multiplication by
contractions. The general operator-norm-weighted left/right ideal bounds are also proved. The canonical
complex trace is exposed through direct Hilbert-basis
`Summable`, `HasSum`, and `tsum` theorems and is cyclic for a trace-class factor and a bounded
factor. General adjoint conjugation preserves trace class, and trace invariance under
`U†U = 1` is derived directly from that cyclicity. Trace-class completeness remains open.

## Fredholm determinant

For absolutely summable diagonal coefficients,

```text
Fredholm.diagonalDet coeff = ∏' i, (1 + coeff i)
```

is proved with convergence, reindexing invariance, finite-support/index reductions, exact zero
characterization, and kernel consequences. The finite-dimensional diagonal specialization is proved
equal to Mathlib's ordinary determinant.

This does not yet define a Fredholm determinant for arbitrary trace-class operators. See
[`fredholm-determinant.md`](fredholm-determinant.md) for the missing general trace-class prerequisites.

## Functional calculus and bounded Dyson theory

`Analysis/FunctionalCalculus/` owns reusable bounded self-adjoint functional-calculus facts used by
Gibbs and entropy constructions.

`Analysis/Dyson/` owns generic Banach-algebra Dyson coefficients, factorial bounds, summability,
Volterra equations, uniqueness, and constant-generator exponential identification. Its canonical
analytic seam is `Dyson.BoundedInteraction`, which keeps the weak identity estimate `‖1‖ ≤ 1`, a
nonnegative majorant, and the interaction norm bound explicitly scoped to `[0, β]`;
`Dyson.ContinuousBoundedInteraction` adds the global continuity required by the Volterra theory.
Neither structure asserts a bound outside the finite interval or strengthens the ambient norm
classes. Quantum and SecondQuantization modules instantiate these hypotheses rather than duplicating
the analytic proof wiring.

## Domain-aware and completed-space analysis

Domain-aware unbounded infrastructure is no longer wholly absent. The repository contains
`LinearPMap`-based unbounded operator tools. Completed-space second quantization provides explicit
maximal diagonal domains with dense-domain/closedness/adjoint/self-adjointness results for real
weights, bounded completed CAR operators, and densely defined closed bosonic weighted shifts whose
creation and annihilation maps are mutual adjoints.

These results do not amount to a general unbounded spectral theory. A 2026-10-05 re-survey of
the pinned Mathlib v4.34.1 revision `d13f23b723b8a846827a245b89c10fc7d3f11612` confirms that
`LinearPMap` still provides the domain-aware adjoint, dense-domain consequences of
self-adjointness, and closedness of self-adjoint operators, but no general unbounded self-adjoint
spectral or functional calculus. The pinned API also does not provide a `LinearPMap` semibounded
quadratic-form package, positivity package, general resolvent calculus, projection-valued spectral
measure calculus, or strongly continuous positive heat-semigroup construction. Comparing the
previous v4.33.1 pin with v4.34.1 reveals no new unbounded functional-calculus layer that closes
this gap.

The project-local resolvent/Cayley/Stone line remains a real-time construction: it builds strongly
continuous unitary evolution from a self-adjoint `LinearPMap` without an unbounded functional
calculus, and it does not define `exp (-β H)`. In particular, the heat operator must not be
introduced by formally analytically continuing Stone evolution or by a power series of unbounded
operator products.
Its consumer-facing endpoint is routed through
`Analysis/Operator/Unbounded.lean`; the Stone approximation, convergence, domain transport, and
generator proofs are consolidated in
`Analysis/Operator/Unbounded/ResolventEvolution.lean`, where stage-specific declarations remain
private. Generic resolvent and Cayley theorems remain available through their independent
modules.

For genuine infinite-dimensional Gibbs theory, the first general equilibrium boundary is therefore
**heat-operator first** rather than Hamiltonian first. The quantum layer may accept, at a fixed
`β > 0`, a bounded positive heat operator `Kβ` together with general trace-class data and
nonzeroness. Positivity plus trace class and nonzeroness imply strictly positive spectral trace, and
`DensityOperator.normalizePositive` is the canonical normalization boundary. The statement that
`Kβ = exp (-β H)` for a semibounded unbounded self-adjoint Hamiltonian belongs to
the upstream domain-aware analysis layer and must retain the Hamiltonian domain and lower-bound
assumptions explicitly. A future heat-semigroup or unbounded functional-calculus implementation can
supply that bridge without changing the density-state normalization API.

The countable pure-point construction remains the spectral-data specialization, not a second
general interface. Its compatibility theorem with the heat-operator boundary should require a
Hilbert basis `b` and energies `E` for which the supplied heat operator satisfies

```text
Kβ (b i) = exp (-β E i) • b i
```

The quantum Gibbs layer now uses this basis action at the general trace-class boundary:
`isTraceClass_iff_purePointGibbsSummable_of_basis_action` identifies `IsTraceClass Kβ` exactly
with Boltzmann summability, and
`heatTrace_eq_purePointPartitionFunction_of_basis_action` identifies the canonical complex trace
with the pure-point partition function. For explicit pure-point heat data,
`inv_partition_smul_heat_eq_purePointGibbsDensityOperator_op` gives the direct operator-level
normalization identity. `DensityOperator.normalizePositive` remains the canonical normalization
boundary for arbitrary positive nonzero trace-class heat data, but the explicit pure-point
compatibility theorem no longer needs to route through it. A general spectral-data-first boundary
should still wait for a genuine spectral-measure/functional-calculus API rather than extending the
pure-point representation beyond what it proves.

The current Gibbs variational and uniqueness proofs do **not** extend to this boundary merely by
replacing the normalized state. They quantify over an arbitrary density operator and use bounded
Hamiltonian matrix elements on every density eigenvector, together with Peierls--Bogoliubov for the
bounded operator exponential. For unbounded pure-point energy data, the existing
`PurePointGibbsEnergyIntegrable` condition controls only the Gibbs distribution itself; it does not
define finite energy for an arbitrary competing density state. A genuine extension therefore needs
a competitor-side finite-energy/domain condition and an inequality mechanism that remains valid
there. In the diagonal/classical subcase this can be developed directly from countable probability
weights and energy summability; a fully quantum noncommuting variational principle requires
additional unbounded relative-entropy/form-domain or lower-semicontinuity infrastructure. The
bounded uniqueness proof also depends on equality in Peierls--Bogoliubov, so it should remain in the
bounded `Observable` layer until such infrastructure exists.

The following remain open or only partially covered:

- trace-class completeness and the broader Schatten hierarchy;
- the Hamiltonian-to-heat bridge for semibounded unbounded self-adjoint operators;
- unbounded self-adjoint functional calculus or equivalent heat-semigroup infrastructure;
- compact-resolvent criteria implying trace-class heat operators;
- completed bosonic ladder product-domain theory;
- general interacting completed-space Dyson theory;
- infinite-volume and thermodynamic limits.

Unbounded objects must retain explicit domains; no result should obtain them by coercing an
unbounded operator to a bounded continuous map.
