# Roadmap — Fermionic Linked Cluster Theorems

**Status: vacuum/free-energy sector complete in formal and finite-dimensional analytic forms; finite-mode two-point sector also proved.**

This page records the current finite-mode fermionic connected-diagram endpoints. It complements
[`second-quantization.md`](second-quantization.md) and
[`second-quantization-status.md`](second-quantization-status.md).

The results here are finite-mode/finite-temperature statements. They do not claim a thermodynamic
limit, trace-class infinite-dimensional Gibbs theory, or a completed-space treatment of general
unbounded operators.

## 1. Vacuum/free-energy formal theorem

For nonzero perturbation order `n`, the canonical coefficientwise endpoint is

```lean
theorem SecondQuantization.Fermionic.
    factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

Schematically, if `Z_D` is the Dyson partition series and `Ẑ_D` its normalized version,

```text
n! [λⁿ] log Ẑ_D(λ)
  = ∑ connected n-vertex quartic Wick diagrams, amplitude(diagram).
```

The factor `n!` converts ordinary power-series coefficients to the finite-set normalization used by
moment–cumulant inversion.

The proof chain is:

```text
component-local orders and component shuffles
                ↓
ordered-simplex shuffle product identity
                ↓
fermionic quartic amplitude factorization
                ↓
connected-diagram formula for Dyson cumulants
                ↓
formal-log coefficient / finite-set cumulant bridge
                ↓
formal Dyson Linked Cluster Theorem
```

The main reusable declarations include

```lean
QuarticDiagram.sum_componentShuffle_orderedSimplexIntegral_eq_prod
quarticWickDiagramAmplitude_eq_prod_restrictComponentConnected
dysonVertexCumulant_quarticInteraction_eq_sum_connectedQuarticWickDiagramAmplitude
Combinatorics.factorial_mul_coeff_logOf_eq_cumulantFromMoment_fin
```

Intermediate proof-routing declarations are intentionally not part of the stable public API unless
they represent a reusable mathematical or physical boundary.

## 2. Vacuum/free-energy analytic theorem

For finite fermionic mode sets, the genuine interacting partition function is

```text
Z(λ) = Tr(exp(-β(H₀ + λV))).
```

The analytic Dyson line proves convergence and identifies the formal coefficients with the Taylor
series of this partition function. After choosing the local normalized logarithm through `log 1 = 0`,
the endpoint is

```lean
theorem SecondQuantization.Fermionic.
    iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude
```

schematically,

```text
(dⁿ/dλⁿ)|₀ log(Z(λ) / Z(0))
  = ∑ connected n-vertex quartic Wick diagrams, amplitude(diagram).
```

Supporting analytic declarations include

```lean
hasSum_dysonTraceCoeff_eq_analyticDysonPartitionFunction
hasFPowerSeriesAt_analyticDysonPartitionFunction
analyticAt_analyticNormalizedLogPartitionFunction_zero
iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_formalCoeff
```

The formal theorem remains the coefficient/combinatorial core; the logarithmic derivative of the
genuine finite-dimensional partition function is the physical vacuum endpoint.

## 3. Two-point linked-cluster theorem

The repository now also proves the two-external-leg version. The diagrammatic expansion separates the
component containing the two external legs from all vacuum components. Fixed external-slot fibers are
reindexed into a Cauchy product, yielding a coefficientwise identity of the form

```text
two-point Dyson coefficient
  = ∑ₘ connected-two-point coefficient(m)
      × normalized-vacuum coefficient(n-m).
```

Passing to formal power series and canceling the normalized vacuum series gives

```lean
theorem SecondQuantization.Fermionic.
    vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
```

from

```text
LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/
  TwoPointDiagramExpansion/CauchySeries.lean
```

Schematically,

```text
(two-point Dyson series) / (vacuum Dyson series)
  = ∑ externally connected two-point diagrams.
```

Thus “correlation functions with external legs” is no longer wholly an open target: the finite-mode
fermionic two-point case is proved. What remains open is the general higher-point/source-insertion
version.

## Current architecture of the two-point proof

The stable conceptual chain is

```text
fixed-external two-point diagrams
        ↓
external connected component + vacuum components
        ↓
component-local amplitude factorization
        ↓
external-slot fiber decomposition
        ↓
ordered vacuum data and shuffle integration
        ↓
coefficientwise Cauchy factorization
        ↓
power-series cancellation
        ↓
vacuum-normalized two-point linked-cluster theorem
```

Recent refactoring removed several one-use routing modules and wrapper theorems from this chain. The
public API should expose physical/combinatorial endpoints, while local reindexing and transport proofs
remain private/local or are inlined when that reduces code.

## Definition of done for the current finite-mode fermionic line

The current milestones are complete because:

- the formal vacuum LCT is exported through the canonical Fermionic Diagrammatics API;
- the finite-dimensional analytic vacuum LCT is exported through Fermionic Perturbation;
- the vacuum-normalized two-point series theorem is exported through the two-point diagram expansion;
- all three endpoints compile without `sorry`;
- the existing sign, coupling, time-order, equal-time, ordered-simplex, and factorial conventions are
  preserved;
- architecture, build/lint, and no-`sorry` CI checks protect the current dependency boundaries.

## Next work

### Higher correlation functions and sources

Generalize the proved two-point theorem to arbitrary time-ordered insertions, multi-leg Green
functions, and source derivatives. This should reuse the Common connectedness/shuffle infrastructure
without rebuilding a parallel routing stack.

### Bosonic perturbation theory

The bosonic line still needs summability-aware product domains, KMS/cyclicity, operator integration,
and Dyson convergence before the connected-diagram machinery can be specialized safely.

### Completed and infinite-mode theory

Completed bounded CAR operators, unbounded Hamiltonian domains, trace-class Gibbs states, infinite-mode
limits, and thermodynamic limits remain separate analytic targets.

### API consolidation

Continue removing dead or one-use public routing declarations when they do not represent reusable
mathematics or a physics-facing endpoint. Prefer direct use of Common/Combinatorics results over
statistics-specific wrapper theorems that merely substitute parameters.
