# Second Quantization — Current Status

This page describes the current architecture, public API, proved endpoints, and analytic boundaries of
`LeanCondensedMatter/SecondQuantization/`. Lean declarations and CI-enforced dependency checks are the
source of truth.

## Scope and current boundary

The foundational algebra is not intrinsically finite-mode:

- `Mode` is an arbitrary type;
- fermionic occupations are finite subsets;
- bosonic occupations are finitely supported functions;
- algebraic Fock vectors are finite linear combinations.

Finiteness is introduced only by results that enumerate all modes or configurations, reconstruct an
operator from a finite basis, or take finite thermal and diagrammatic sums.

The fermionic line is complete through the coefficientwise and finite-dimensional analytic Linked
Cluster Theorems. Those analytic results remain finite-mode and finite-dimensional.

The repository also contains an initial completed fermionic representation on
`ℓ²(Fermionic.Occupation Mode, ℂ)`, with an injective dense algebraic core and a bounded single-mode
number operator. It does not yet provide completed creation and annihilation operators, general
unbounded Hamiltonian domains, trace-class infinite-dimensional Gibbs states, infinite-mode thermal
limits, or a thermodynamic limit.

A finite bosonic mode type still has an infinite occupation basis. The bosonic line therefore uses
explicit summability domains and cannot inherit the finite-configuration trace and operator-integral
interfaces merely by changing statistics.

## Canonical public imports

The full public entry point is:

```lean
import LeanCondensedMatter.SecondQuantization
```

Responsibility-specific code may import a leaf umbrella:

| Area | Common import | Fermionic import | Bosonic import |
|---|---|---|---|
| Algebra | `LeanCondensedMatter.SecondQuantization.Common.Algebra` | `LeanCondensedMatter.SecondQuantization.Fermionic.Algebra` | `LeanCondensedMatter.SecondQuantization.Bosonic.Algebra` |
| Imaginary time | `LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime` | `LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime` | `LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime` |
| Thermal theory | `LeanCondensedMatter.SecondQuantization.Common.Thermal` | `LeanCondensedMatter.SecondQuantization.Fermionic.Thermal` | `LeanCondensedMatter.SecondQuantization.Bosonic.Thermal` |
| Perturbation | `LeanCondensedMatter.SecondQuantization.Common.Perturbation` | `LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation` | not exposed until the convergence-aware operator-integral boundary exists |
| Diagrammatics | `LeanCondensedMatter.SecondQuantization.Common.Diagrammatics` | `LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics` | `LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics` |
| Completed fermionic space | — | `LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace` | not yet exposed |

## Ownership and dependency direction

The declaration-owning namespaces are:

```lean
SecondQuantization.Common
SecondQuantization.Fermionic
SecondQuantization.Bosonic
```

The dependency direction is:

```text
Analysis, Combinatorics
          ↓
SecondQuantization.Common
          ↓
SecondQuantization.Fermionic, SecondQuantization.Bosonic
```

`Analysis/` owns reusable analytic and linear-algebraic infrastructure. `Combinatorics/` owns results
about partitions, pairings, cumulants, and finite products that do not require a second-quantized
interpretation. `SecondQuantization.Common` owns statistics-independent constructions that still use
occupation bases, Fock operators, exchange statistics, thermal functionals, or diagrammatic data.

A declaration under `Fermionic` or `Bosonic` should remain public only when it contributes a
statistics-specific operator, sign, occupation rule, energy, convergence statement, physical name,
or analytic hypothesis. Parameter-substitution wrappers around a Common theorem are not separate
public APIs.

The architecture and namespace boundaries are checked by
`scripts/check_second_quantization_architecture.py`. The dimension-independent foundational mode
boundary is checked by `scripts/check_second_quantization_mode_boundary.py`.

## Shared statistics-independent layer

| Area | Main modules | Current result |
|---|---|---|
| Algebraic Fock infrastructure | `Common/Algebra/` | finite-support occupation interfaces, basis states, matrix coefficients, diagonal maps, grading, exchange signs, and finite-configuration infrastructure where required |
| Imaginary-time infrastructure | `Common/ImaginaryTime/` | diagonal evolution, interaction-picture matrix coefficients, continuity and integrability, time ordering, and KMS rotation |
| Thermal functionals | `Analysis/NormalizedEndomorphismFunctional.lean`, `Common/Thermal/` | normalized functionals, finite weighted traces, Gibbs infrastructure, and abstract Bloch–de Dominicis recursion |
| Finite operator integration | `Common/Perturbation/FiniteOperatorIntegral.lean`, `FiniteAnalyticBridge.lean` | coefficientwise operator integration and its finite-dimensional continuous-operator realization |
| Dyson coefficients | `Common/Perturbation/DysonExpansion.lean`, `DysonTimeIndependent.lean` | algebraic Dyson recursion and the algebraic/analytic time-independent specialization |
| Analytic Dyson evolution | `Common/Perturbation/ContinuousDyson.lean`, `AnalyticDyson*.lean` | factorial bounds, norm convergence, the Volterra equation, uniqueness, and the exact exponential identity |
| Dyson trace series | `Common/Perturbation/DysonTraceSeries.lean`, `AnalyticDysonTrace.lean` | formal trace coefficients, convergent trace series, and Taylor-series packaging |
| Quartic diagram data | `Common/Diagrammatics/` | labels, ordered data, connectedness, component restriction and reassembly, decomposition equivalences, and component-local orders |
| Ordered-simplex products | `Analysis/OrderedSimplex/`, `Common/Diagrammatics/ComponentOrderedSimplexProduct.lean` | shuffle sums equal products of component-local ordered-simplex integrals |
| Cumulants and connected diagrams | `Combinatorics/` | moment–cumulant inversion, multiplicative diagram weights, connected decomposition, and formal-log coefficient identities |

## Fermionic line

The canonical algebraic names distinguish the two uncompleted representations explicitly:

```lean
Fermionic.Occupation
Fermionic.OccupationFock
Fermionic.AlgebraicFock
Fermionic.vacuum
Fermionic.particleNumber
```

`OccupationFock Mode` is the free vector space on finite occupation subsets of a chosen mode type.
`AlgebraicFock 𝓗₁` is the basis-independent exterior algebra of the one-particle space. A chosen
one-particle basis gives the explicit `AlgebraicFock.occupationEquiv` between them. Neither name denotes the
completed `ℓ²` representation.

The finite-mode fermionic API includes:

- creation and annihilation operators, CAR, grading, and free/interacting Hamiltonians;
- free imaginary-time evolution and `Fermionic.interactionPicture`;
- finite free Gibbs weights, partition functions, contractions, and the finite-temperature
  Bloch–de Dominicis theorem;
- the physical Dyson partition coefficients and normalized formal logarithm;
- the finite-dimensional interacting partition function and its Taylor series;
- non-diagonal quartic interactions, local-leg semantics, Wick diagrams, component decomposition,
  shuffle factorization, cumulants, and connected-diagram formulas.

## Formal and analytic Linked Cluster Theorems

The coefficientwise endpoint is:

```lean
factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

For `n ≠ 0`, it identifies

```text
n! [λⁿ] log(normalized Dyson partition series)
```

with the sum of amplitudes of connected `n`-vertex quartic Wick diagrams.

The finite-dimensional analytic endpoint is obtained through:

- `hasSum_dysonTraceCoeff_eq_analyticDysonPartitionFunction`;
- `hasFPowerSeriesAt_analyticDysonPartitionFunction`;
- `analyticAt_analyticNormalizedLogPartitionFunction_zero`;
- `iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_formalCoeff`;
- `iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude`.

The formal layer remains a reusable coefficient calculus. The analytic partition function and its
connected logarithmic derivatives are the physical finite-mode endpoint.

## Fermionic capability matrix

| Capability | Status | Main result or module |
|---|---:|---|
| Algebraic Fock and CAR | done | `Fermionic.Algebra` |
| Free imaginary-time evolution | done | `Fermionic.ImaginaryTime` |
| Finite free Gibbs theory | done | `Fermionic.Thermal` |
| General finite-temperature pairing theorem | done | `Common/Thermal/BlochDeDominicis/Induction.lean` with fermionic hypotheses |
| Discrete and continuous Dyson infrastructure | done | `Common.Perturbation` specialized by `fermionEnergy` |
| Physical partition coefficients and formal logarithm | done | `Fermionic/Perturbation/DysonPartitionSeries.lean` |
| Analytic partition function and Taylor series | done | `Fermionic/Perturbation/AnalyticDysonPartitionFunction.lean` |
| Analytic/formal logarithm identification | done | `AnalyticLinkedClusterRecurrence.lean`, `AnalyticLinkedClusterIdentification.lean` |
| Full quartic Wick amplitude | done | `Fermionic/Diagrammatics/WickDiagram/Amplitude.lean` |
| Dyson diagram expansion | done | `Fermionic/Diagrammatics/DysonDiagramExpansion.lean` |
| Full amplitude factorization | done | `WickDiagram/AmplitudeFactorization.lean` |
| Connected-diagram cumulant theorem | done | `DysonConnectedDiagramExpansion.lean` |
| Formal Dyson LCT | done | `DysonLinkedClusterTheorem.lean` |
| Analytic finite-mode Dyson LCT | done | `Fermionic/Perturbation/AnalyticLinkedClusterTheorem.lean` |

## Completed fermionic representation

`Fermionic/CompletedSpace/Basic.lean` provides:

- `Fermionic.CompletedFockSpace Mode := ℓ²(Fermionic.Occupation Mode, ℂ)`;
- canonical occupation basis vectors;
- the coordinate-preserving inclusion `algebraicToCompleted`;
- injectivity and dense range of the algebraic inclusion;
- a bounded single-mode occupation projection;
- agreement of the completed and algebraic number operators on the algebraic core.

This establishes the completed representation without treating all algebraic operators as bounded.
The remaining operator and thermal boundaries are documented in
[`completed-space-and-infinite-mode.md`](completed-space-and-infinite-mode.md).

## Bosonic line and convergence boundary

The bosonic line includes:

- occupation states `Mode →₀ ℕ`, algebraic Fock space, normalized ladder operators, CCR, number
  operators, and grading;
- free diagonal and interaction-picture evolution;
- convergent free partition and particle-number series under explicit positivity assumptions;
- free two-point coefficients and Bloch–de Dominicis base results;
- `ConvergenceAwareGibbsFunctional`, whose observable domain records Gibbs-numerator summability and
  is closed under finite linear combinations;
- quartic interaction labels, local-leg semantics, ordered diagrams, connected components, and
  componentwise scalar prefactors.

The convergence-aware functional does not assert closure under operator products or integrals.
Remaining analytic requirements are:

1. product-domain closure for the observables appearing in Wick recursion;
2. summability-aware KMS and trace-cyclicity statements;
3. an operator-valued integration interface compatible with the chosen domains;
4. convergence hypotheses for Dyson coefficients and traces;
5. a bosonic full-amplitude and connected-diagram specialization built on those interfaces.

No finite-basis assumption on `Bosonic.Occupation Mode` should be introduced to bypass these
requirements.

## Refactoring priorities

- keep one authoritative owner for every construction;
- remove statistics-specific declarations that only substitute parameters into Common results;
- retain physics-facing specializations with independent semantic value;
- move reusable mathematics upstream only when the target abstraction is genuinely independent of
  second quantization;
- keep proof-only transport, uniqueness, and basis calculations private or local;
- regroup long diagrammatic stacks only when a file boundary exposes proof internals rather than a
  reusable domain concept;
- keep CI focused on dependency direction, namespace ownership, canonical imports, and forbidden
  classes of compatibility layer.

## Separate research tracks

The following are extensions rather than missing steps of the finite-mode fermionic LCT:

- low-order explicit examples;
- time-ordered correlation functions with external operators;
- convergence-aware bosonic Dyson and linked-cluster theory;
- bounded completed creation and annihilation operators and completed CAR;
- domains and functional calculus for unbounded operators;
- trace-class Gibbs states, finite-mode compatibility, infinite-mode limits, and thermodynamic
  limits.
