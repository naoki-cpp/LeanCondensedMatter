# Fermionic linked-cluster theorems

The current proved line covers finite-mode fermionic zero-external-leg/partition-function and
two-point connected-diagram expansions. It does not claim a thermodynamic limit or a general
higher-point expansion.

## Formal log-partition theorem

For nonzero perturbation order `n`,

```lean
factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude
```

identifies

```text
n! [λⁿ] log(normalized Dyson partition series)
```

with the sum of connected `n`-vertex quartic Wick-diagram amplitudes.

The statistics-independent formal core has two kernel-checked routes. The inversion route is
`Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution`; the independent replica route is
`Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution_replica`. The replica theorem
takes a unit-constant formal power series, a multiplicative connected decomposition, and equality
of the bundled factorial-normalized moment function with the normalized object moment, then
identifies the formal-log coefficient with the connected contribution using only the forward moment
decomposition.
The canonical fermionic theorem consumes this replica route; its model-specific obligation is the
Dyson-moment/Wick-diagram identification, packaged once as
`dysonPartitionSeriesMoment_eq_wickDiagramObjectMoment` in
`Fermionic.Diagrammatics.DysonDiagramExpansion.Moment`. The independent inversion route applies
`Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution` to that same moment equality.
It kernel-checks the canonical connected-diagram statement as an `example`, without introducing
a fermionic cumulant definition or a duplicate public theorem.
No source-functional wrapper is required for this formal partition-function endpoint.

The finite-configuration Dyson trace coefficients and series are owned by
`Common.Perturbation.DysonTraceSeries`. Their normalized coefficients and labelled vertex moments
use `PowerSeries.normalizeByConstantCoeff` and `Combinatorics.powerSeriesMomentCoeff` directly;
there are no parallel Dyson-specific normalization or moment definitions. The Common trace-series owner proves the normalized coefficient's finite Gibbs-expectation
identity. Fermionic connected-diagram statements use the specialized
`Common.dysonTraceSeries (fermionEnergy ε) β V` and its `PowerSeries.normalizeByConstantCoeff`/
`PowerSeries.logOf` operations directly, without a parallel fermionic partition-series API.
The fermionic Dyson pairing proof uses the generic normalized-coefficient theorem together
with `freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation` directly; no separate
fermionic vertex-moment adapter is needed.

## Analytic log-partition theorem

For finite fermionic mode sets,

```text
Z(λ) = Tr(exp(-β(H₀ + λV))).
```

The analytic Dyson theory identifies the formal coefficients with the Taylor expansion of `Z` and
proves

```lean
iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude
```

for the local normalized logarithm of the interacting finite-temperature partition function. The
generic analytic/formal logarithm bridge is owned by `Analysis.PowerSeries.AnalyticLog`, its
finite-configuration Dyson specialization by `SecondQuantization.Common.Perturbation.AnalyticLinkedCluster`,
and the concrete connected-diagram endpoint by `Fermionic.Diagrammatics.LinkedCluster.Analytic`.

## Two-point theorem

The two-point expansion separates the component containing the two external legs from
zero-external-leg components, yielding the series factorization

```text
two-point Dyson series
  = externally connected two-point series × normalized Dyson partition series.
```

Generic power-series inverse cancellation then gives

```lean
partitionFunctionNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
```

from `Fermionic/Diagrammatics/TwoPointDiagramExpansion/Series/CauchySeries.lean`.

Partition-function normalization divides by the free-state-normalized zero-external-leg Dyson
partition series. It removes vacuum bubbles, not disconnected externally supported components.
Thus the analogous higher-point quotient is not generally a connected correlation function.

## Statistics-independent moment boundary

Both generic endpoints consume the same normalized finite-set boundary:
`Combinatorics.powerSeriesMomentSetFunction` is compared with
`MultiplicativeWeight.normalizedObjectMoment`. The inversion route extracts connected data by
finite-set cumulant inversion, while the replica route converts that bundled equality internally to
the forward coefficient identity needed by the replica polynomial proof. Both routes identify the
same formal-log coefficient with the connected-object contribution.

`Finpartition.IsIndependentAcross` and the associated cumulant-vanishing results apply to
moment functions over a commutative ring; no choice of quantum ensemble or Wick/Gaussian property
enters their proofs. A concrete state must separately establish the moment-factorization hypothesis.

The bosonic physical Dyson connected theorem uses the same normalized finite-set and
`MultiplicativeWeight` machinery directly. Its Dyson-to-diagram expansion, component
factorization, and series-to-object-moment identity are separated under
`Bosonic.Diagrammatics.Quartic.Thermal.DysonExpansion` as `Pairing`, `Factorization`,
and `Moment` modules. Its finite-mode quartic Dyson coefficients are Gibbs-summable at
every fixed perturbation order through finite thermal-field expansions. Statistics
enter only in concrete moment realizations, pairing weights, and amplitudes. This does not yet give a
genuine analytic bosonic partition function: the missing step is all-order interacting convergence
on the infinite occupation space. No source-functional wrapper is part of the current zero-source
LCT API. A source-functional abstraction should be introduced only when pre-normalized external
insertions and higher-point source consumers give it independent semantics.

## Low-order identities

The explicit order-`1`, order-`2`, and order-`3` formal-log formulas are the generic theorems in
`Analysis/PowerSeries/LowOrderLog.lean`, applied to the normalized fermionic Dyson trace series.
They are illustrated in [the low-order example](../examples/fermionic-lct-low-order.md).
The former fermionic-only `LinkedCluster/LowOrder.lean` specializations had no Lean consumers and
were removed rather than retained as duplicate public declarations. The generic formal-log proofs
remain kernel-checked; the opt-in checks of these exact fermionic specializations are no longer
compiled separately. Connected-diagram and analytic low-order statements still follow by
specializing the canonical general formal and analytic endpoints.

## Replica-method proof track

The independent algebraic replica track is proved. For a finite support `S`,
`Finpartition.replicaPolynomial` records the component-replica count

```text
R_S(N) = ∑_{π : Finpartition S} N^(number of blocks of π) × partitionProduct κ π.
```

For nonempty `S`, `Finpartition.replicaPolynomial_coeff_one` extracts the connected
contribution from the coefficient linear in `N`. Replica colourings give the combinatorial
interpretation of the factor `N^(number of blocks)`.

On the formal-power-series side, `PowerSeries.replicaCoeffPolynomial` is the fixed-order
replica-count polynomial. Its evaluation at a natural replica number reproduces the corresponding
factorial-normalized coefficient of a power, and
`PowerSeries.replicaCoeffPolynomial_coeff_one` identifies its linear replica coefficient with the
same-order coefficient of `logOf`.

`Combinatorics.replicaCoeffPolynomial_eq_replicaPolynomial` identifies the power-series and
finite-set replica polynomials under the forward moment hypothesis, and
`Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution_replica` gives the generic
linked-cluster endpoint without Möbius/cumulant inversion. The finite-mode fermionic theorem
`factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude`
is proved through this replica endpoint while retaining its existing public API.

The import boundaries are enforced in both directions by source-topology rules.
`replicaLinkedClusterIndependence` prevents the generic replica bridge and canonical fermionic
specialization from reaching `Combinatorics.Cumulant.Inversion`,
`ConnectedDecompositionInversion`, or `Analysis.PowerSeries.Cumulant`.
`inversionLinkedClusterIndependence` prevents the concrete inversion specialization from reaching
the power-series or finite-set replica modules. Thus neither concrete proof route can silently
depend on the other.

## Higher-point diagram-selection boundary

For arbitrary fixed external fields, `ExternalComponentReplicaPolynomial.lean` defines a
finite-order polynomial weighted by the number of externally supported connected components.
Its linear coefficient selects fully externally connected signed diagram amplitudes, starting
from vacuum-free diagrams. This is an exact combinatorial selection statement, **not** a
source-functional generating identity, an analytic replica-number continuation, or a general
higher-point cumulant expansion. The latter bridges remain open.

## Open work

- source-functional realizations of higher-point moments and their connected/cumulant normalization;
- arbitrary higher-point and source-insertion connected expansions, including a source-functional layer if required by concrete consumers;
- bosonic interacting Dyson convergence and analytic linked-cluster theory;
- interacting completed-space perturbation theory with explicit product domains;
- infinite-mode and thermodynamic limits under explicit analytic hypotheses.
