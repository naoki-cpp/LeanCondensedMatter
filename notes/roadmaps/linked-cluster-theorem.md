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

`Combinatorics.powerSeriesMomentSetFunction` packages factorial-normalized coefficients of a
unit-constant formal power series as a `NormalizedSetFunction`. Connected-decomposition consumers
compare that moment function directly with `MultiplicativeWeight.normalizedObjectMoment`; the
generic theorem `Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution` then identifies
the corresponding formal-log coefficient with the connected-object contribution.

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

An independent algebraic proof track should recover the formal linked-cluster endpoint by replica
counting rather than partition-lattice Möbius inversion. For a finite support `S`, the
statistics-independent core is a polynomial in a formal replica-count variable `N`,

```text
R_S(N) = ∑_{π : Finpartition S} N^(number of blocks of π) × partitionProduct κ π.
```

For nonempty `S`, the coefficient linear in `N` receives a contribution only from the one-block
partition and therefore equals `κ S`. The factor `N^(number of blocks)` should also be identified
with the number of independent replica labelings of the connected components, so the formal
polynomial retains the combinatorial meaning of the replica construction.

On the power-series side, the target is a fixed-order replica-count polynomial whose evaluation at
a natural number `n` gives the corresponding factorial-normalized coefficient of `Z^n`. Its
coefficient linear in the replica-count variable should equal the same-order coefficient of
`logOf Z`. This replaces an analytic `n → 0` continuation by finite polynomial coefficient
extraction.

The proof should reuse the forward connected-decomposition structure and multiplicative-weight
factorization, but remain independent of `ConnectedDecompositionInversion`,
`cumulantFromMoment`, and the existing formal-log/cumulant endpoint. This dependency boundary is
what makes the replica route a meaningful kernel-checked cross-check of the current Möbius proof.

Reusable finite-set replica machinery belongs in `Combinatorics`; generic formal power-series
replica algebra belongs in `Analysis/PowerSeries`. Fermionic diagrammatics should consume those
generic results only at the final Dyson/Wick specialization. Public declarations should represent
independent replica or polynomial concepts rather than duplicate aliases for the existing
linked-cluster endpoint.

## Open work

- pre-normalized arbitrary higher-point source moments and their vacuum normalization;
- arbitrary higher-point and source-insertion connected expansions, including a source-functional layer if required by concrete consumers;
- convergence-aware bosonic Dyson and linked-cluster theory;
- interacting completed-space perturbation theory with explicit product domains;
- infinite-mode and thermodynamic limits under explicit analytic hypotheses.
