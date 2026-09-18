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

The statistics-independent formal core is owned by
`Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution`. It takes a unit-constant formal
power series, a multiplicative connected decomposition, and equality between the series'
factorial-normalized finite-set moments and the decomposition's normalized object moments; it then
identifies the formal-log coefficient directly with the connected-object contribution. The
fermionic theorem is a concrete consumer: its only model-specific obligation at this boundary is the
Dyson-moment/Wick-diagram identification. No source-functional wrapper is required for this formal
partition-function endpoint.

The normalized coefficients themselves,
`normalizedDysonPartitionCoeff`, belong to `Fermionic.Perturbation.DysonPartitionSeries` together
with the normalized-series coefficient theorem and formal logarithm. `DysonVertexMoment` owns only
the labelled finite-set moment boundary, its Gibbs expectation bridge used by diagrammatics, and the
Dyson generating-functional specialization.

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
analytic/formal coefficient bridge remains in `Fermionic.Perturbation.AnalyticLinkedCluster`; the
concrete connected-diagram endpoint is owned by `Fermionic.Diagrammatics.LinkedCluster.Analytic`.

## Two-point theorem

The two-point expansion separates the component containing the two external legs from
zero-external-leg components, yielding the series factorization

```text
two-point Dyson series
  = externally connected two-point series × normalized Dyson partition series.
```

Generic power-series inverse cancellation then gives

```lean
vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
```

from `Fermionic/Diagrammatics/TwoPointDiagramExpansion/Series/CauchySeries.lean`.

Here `vacuumNormalized` is the Lean identifier for division by the zero-external-leg Dyson partition
series; it does not mean that the thermal state is a vacuum state. Vacuum normalization is distinct
from full source connectedness for higher-point external insertions.

## Formal source-functional layer

`Common.Perturbation.GeneratingFunctional` provides the statistics-independent normalized source
boundary. `GeneratingFunctional` stores normalized finite-set source moments over a commutative
coefficient ring, `connected` applies the finite-set cumulant transform, and
`GeneratingFunctional.connected_moment` reconstructs the normalized moments.
`GeneratingFunctional.connected_eq_connectedContribution` is the statistics-independent
source/diagram seam: when normalized source moments agree with the normalized object moments of a
multiplicative connected decomposition, connected source coefficients equal its connected-object
contribution. This seam is for consumers that genuinely carry source-functional semantics. The
bosonic coefficientwise connected theorem applies the underlying statistics-independent
`MultiplicativeWeight` cumulant theorem directly, while the fermionic zero-source formal LCT now
uses the lower generic power-series/connected-decomposition theorem directly. Statistics do not
enter either bridge; they remain in concrete source/moment realizations and in pairing weights and
amplitudes. `powerSeriesGeneratingFunctional` wraps the generic
`Combinatorics.powerSeriesMomentSetFunction` when a source-functional view is actually needed.

`Fermionic.dysonVertexGeneratingFunctional` is the concrete normalized Dyson specialization. The
quartic Wick layer supplies the model-specific amplitudes and fermionic signs. Pre-normalized
external-insertion moments, their vacuum normalization, Grassmann variables, and arbitrary
higher-point connected diagram expansions remain downstream work.

## Low-order identities

Orders `1`, `2`, and `3` remain available as explicit readable examples and regression theorems in

```text
Fermionic/Diagrammatics/LinkedCluster/LowOrder.lean
Fermionic/Diagrammatics/LinkedCluster/AnalyticLowOrder.lean
```

They are opt-in modules rather than part of the canonical `LinkedCluster` umbrella. The umbrella
exports the general formal and analytic endpoints.

## Open work

- pre-normalized arbitrary higher-point source moments and their vacuum normalization;
- arbitrary higher-point and source-insertion connected expansions using the formal source-functional layer;
- convergence-aware bosonic Dyson and linked-cluster theory;
- interacting completed-space perturbation theory with explicit product domains;
- infinite-mode and thermodynamic limits under explicit analytic hypotheses.
