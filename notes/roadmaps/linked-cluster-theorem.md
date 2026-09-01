# Fermionic linked-cluster theorems

The current proved line covers finite-mode fermionic vacuum/free-energy and two-point connected
diagram expansions. It does not claim a thermodynamic limit or a general higher-point expansion.

## Formal vacuum theorem

For nonzero perturbation order `n`,

```lean
factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

identifies

```text
n! [λⁿ] log(normalized Dyson partition series)
```

with the sum of connected `n`-vertex quartic Wick-diagram amplitudes. The reusable chain is

```text
component factorization
  → connected Dyson cumulants
  → moment-cumulant / formal-log bridge
  → formal linked-cluster theorem.
```

## Analytic vacuum theorem

For finite fermionic mode sets,

```text
Z(λ) = Tr(exp(-β(H₀ + λV))).
```

The analytic Dyson theory identifies the formal coefficients with the Taylor expansion of `Z` and
proves

```lean
iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude
```

for the local normalized logarithm of the interacting partition function.

## Two-point theorem

The two-point expansion separates the component containing the two external legs from vacuum
components, yielding a Cauchy factorization of the Dyson coefficients. Power-series cancellation then
gives

```lean
vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
```

from `Fermionic/Diagrammatics/TwoPointDiagramExpansion/CauchySeries.lean`.

Schematically,

```text
(two-point Dyson series) / (vacuum Dyson series)
  = externally connected two-point diagrams.
```

The public API should expose these physical/combinatorial endpoints; proof-only reindexing and
transport declarations remain private/local unless independently reusable.

## Open work

- arbitrary higher-point and source-insertion connected expansions;
- convergence-aware bosonic Dyson and linked-cluster theory;
- interacting completed-space perturbation theory with explicit product domains;
- infinite-mode and thermodynamic limits under explicit analytic hypotheses.
