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
takes a unit-constant formal power series, a multiplicative connected decomposition, and direct
equality between factorial-normalized coefficients and object moments, then identifies the
formal-log coefficient with the connected contribution using only the forward moment decomposition.
The canonical fermionic theorem consumes this replica route; its model-specific obligation is the
Dyson-moment/Wick-diagram identification. No source-functional wrapper is required for this formal
partition-function endpoint.

The normalized coefficients themselves,
`normalizedDysonPartitionCoeff`, belong to `Fermionic.Perturbation.DysonPartitionSeries` together
with the normalized-series coefficient theorem and formal logarithm. `DysonVertexMoment` owns only
the labelled finite-set moment boundary and its Gibbs expectation bridge used by diagrammatics.

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

## Statistics-independent moment boundary

The inversion route packages factorial-normalized coefficients with
`Combinatorics.powerSeriesMomentSetFunction` and compares that normalized finite-set function with
`MultiplicativeWeight.normalizedObjectMoment`. The replica route instead consumes the direct
coefficient identity against `MultiplicativeWeight.objectMoment`, avoiding cumulant inversion.
Both routes identify the same formal-log coefficient with the connected-object contribution.

The bosonic coefficientwise connected theorem uses the same normalized finite-set and
`MultiplicativeWeight` machinery directly. Statistics enter only in concrete moment realizations,
pairing weights, and amplitudes. No source-functional wrapper is part of the current zero-source LCT
API. A source-functional abstraction should be introduced only when pre-normalized external
insertions and higher-point source consumers give it independent semantics.

## Low-order identities

Orders `1`, `2`, and `3` remain available as explicit readable formal-log examples and
regression theorems in

```text
Fermionic/Diagrammatics/LinkedCluster/LowOrder.lean
```

The module records only the moment-cumulant subtraction polynomials. Connected-diagram and analytic
low-order statements are obtained by specializing the canonical general formal and analytic
endpoints rather than by separate public wrappers. `LowOrder` remains opt-in and is not part of
the canonical `LinkedCluster` umbrella.

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

The import boundary is enforced by the `replicaLinkedClusterIndependence` source-topology rule:
the generic replica bridge and the fermionic specialization cannot reach
`Combinatorics.Cumulant.Inversion`, `ConnectedDecompositionInversion`, or
`Analysis.PowerSeries.Cumulant`. This keeps the replica route a genuine kernel-checked cross-check
of the inversion proof.

## Open work

- pre-normalized arbitrary higher-point source moments and their vacuum normalization;
- arbitrary higher-point and source-insertion connected expansions, including a source-functional layer if required by concrete consumers;
- convergence-aware bosonic Dyson and linked-cluster theory;
- interacting completed-space perturbation theory with explicit product domains;
- infinite-mode and thermodynamic limits under explicit analytic hypotheses.
