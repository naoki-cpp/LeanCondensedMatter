# Second Quantization — Current Status

This page summarizes the current architecture and proved results in
`LeanCondensedMatter/SecondQuantization/`. The canonical-API migration is tracked by issue #345; its
migration map is [`second-quantization-refactor.md`](second-quantization-refactor.md). The development
history of the fermionic Linked Cluster Theorem is recorded in
[`linked-cluster-theorem.md`](linked-cluster-theorem.md).

The source of truth for every completed claim is the referenced Lean declaration. The completed
modules compile without `sorry`.

## Scope and current boundary

The finite-mode fermionic line is complete through both the coefficientwise and finite-dimensional
analytic Linked Cluster Theorems. In particular, the repository now contains:

- finite-mode fermionic algebra, imaginary-time evolution, thermal theory, Dyson coefficients, Wick
  diagrams, and connected-component factorization;
- the formal coefficient theorem for the normalized Dyson partition series;
- a norm-convergent finite-dimensional analytic Dyson evolution and its exact operator-exponential
  identity;
- identification of the Dyson trace coefficients with the Taylor series of
  `Tr exp(-β (H₀ + λV))`;
- identification of logarithmic derivatives with formal logarithm coefficients and connected quartic
  Wick-diagram amplitudes.

The analytic results are finite-mode and finite-dimensional. They do not provide completed-space
unbounded-operator theory, infinite-mode limits, or thermodynamic limits.

The bosonic line mirrors the statistics-independent and algebraic layers where the mathematics is
valid, but a finite set of bosonic modes still has an infinite occupation basis. General bosonic
Gibbs, operator-integration, Dyson, and LCT APIs therefore remain blocked on explicit summability-aware
interfaces.

## Canonical public imports

The single full public entry point is:

```lean
import LeanCondensedMatter.SecondQuantization
```

Responsibility-specific code may instead import one of the leaf umbrellas:

| Area | Common import | Fermionic import | Bosonic import |
|---|---|---|---|
| Algebra | `LeanCondensedMatter.SecondQuantization.Common.Algebra` | `LeanCondensedMatter.SecondQuantization.Fermionic.Algebra` | `LeanCondensedMatter.SecondQuantization.Bosonic.Algebra` |
| Imaginary time | `LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime` | `LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime` | `LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime` |
| Thermal theory | `LeanCondensedMatter.SecondQuantization.Common.Thermal` | `LeanCondensedMatter.SecondQuantization.Fermionic.Thermal` | `LeanCondensedMatter.SecondQuantization.Bosonic.Thermal` |
| Perturbation | `LeanCondensedMatter.SecondQuantization.Common.Perturbation` | `LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation` | not exposed without a convergence-aware interface |
| Diagrammatics | `LeanCondensedMatter.SecondQuantization.Common.Diagrammatics` | `LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics` | `LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics` |

The former exact compatibility imports `LeanCondensedMatter.SecondQuantization.Common`,
`.Fermionic`, and `.Bosonic` are removed. Old paths are not retained through forwarding modules.

## Ownership and dependency direction

The canonical declaration namespaces are:

```lean
SecondQuantization.Common
SecondQuantization.Fermionic
SecondQuantization.Bosonic
```

The dependency direction is one way:

```text
Analysis, Combinatorics
          ↓
SecondQuantization.Common
          ↓
SecondQuantization.Fermionic, SecondQuantization.Bosonic
```

`Common/` does not import `Fermionic/` or `Bosonic/`, and generic `Analysis/` and `Combinatorics/`
modules do not import physics modules. The architecture and declaration/path namespace checks are run
by `scripts/check_second_quantization_architecture.py` in CI.

## Shared statistics-independent layer

| Area | Main modules | Current result |
|---|---|---|
| Algebraic Fock infrastructure | `Common/Algebra/` | Basis states, matrix coefficients, diagonal maps, grading, exchange signs, and finite configuration infrastructure. |
| Imaginary-time infrastructure | `Common/ImaginaryTime/` | Diagonal evolution, interaction-picture matrix coefficients, continuity/integrability results, time ordering, and KMS rotation. |
| Thermal functionals | `Analysis/NormalizedEndomorphismFunctional.lean`, `Common/Thermal/` | Normalized functionals, finite weighted traces, Gibbs infrastructure, and the abstract Bloch–de Dominicis theorem. |
| Finite operator integration | `Common/Perturbation/FiniteOperatorIntegral.lean`, `FiniteAnalyticBridge.lean` | Coefficientwise integration and its continuous-operator realization for finite configuration types. |
| Discrete Dyson coefficients | `Common/Perturbation/DysonExpansion.lean`, `DysonExpansionVerification.lean` | The authoritative algebraic coefficient recursion and time-independent coefficient formula. |
| Analytic Dyson evolution | `Common/Perturbation/ContinuousDyson.lean`, `AnalyticDyson*.lean` | Factorial norm bounds, norm convergence, Volterra equation, uniqueness, and the exact exponential identity. |
| Dyson trace series | `Common/Perturbation/DysonTraceSeries.lean`, `AnalyticDysonTrace.lean` | Formal trace coefficients, convergent trace series, and Taylor-series packaging. |
| Quartic diagram data | `Common/Diagrammatics/` | Labels, ordered data, connectedness, component restriction/reassembly, decomposition equivalence, and component-local orders. |
| Ordered-simplex shuffle calculus | `Analysis/OrderedSimplex/`, `Common/Diagrammatics/ComponentOrderedSimplexProduct.lean` | Binary and finite-family shuffle sums equal products of local ordered-simplex integrals. |
| Cumulants and connected diagrams | `Combinatorics/` | Finite-set moment–cumulant inversion, multiplicative diagram weights, connected decomposition, and the formal-log coefficient bridge. |

The former fermionic discrete- and continuous-Dyson forwarding modules are deleted. Fermionic code
specializes the authoritative Common constructions explicitly with `fermionEnergy ε`.

## Fermionic line

The canonical core names are:

```lean
Fermionic.Occupation
Fermionic.FockSpace
Fermionic.vacuum
Fermionic.particleNumber
```

The finite-mode fermionic API includes:

- creation and annihilation operators, CAR, grading, and free/interacting Hamiltonians;
- free imaginary-time evolution and the physics-facing `Fermionic.interactionPicture`;
- finite free Gibbs weights, partition functions, two-point functions, contractions, and the
  finite-temperature Bloch–de Dominicis theorem;
- the physical partition coefficient `Fermionic.dysonPartitionCoeff` and formal normalized logarithm;
- the genuine interacting partition function `Fermionic.analyticDysonPartitionFunction`;
- a non-diagonal quartic interaction, local-leg semantics, ordered Wick diagrams, full amplitudes,
  and the Dyson diagram expansion;
- component decomposition, component shuffle calculus, full-amplitude factorization, cumulants, and
  connected-diagram formulas;
- both formal and analytic finite-mode Linked Cluster Theorems.

## Formal and analytic Linked Cluster Theorems

The coefficientwise theorem is:

```lean
factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

For `n ≠ 0`, it identifies

```text
n! [λⁿ] log(normalized Dyson partition series)
```

with the sum of amplitudes of connected `n`-vertex quartic Wick diagrams.

The finite-dimensional analytic chain is also complete:

- `hasSum_dysonTraceCoeff_eq_analyticDysonPartitionFunction` identifies the specialized Common Dyson
  trace series with `analyticDysonPartitionFunction`;
- `hasFPowerSeriesAt_analyticDysonPartitionFunction` packages those coefficients as the Taylor series
  at zero coupling;
- `analyticAt_analyticNormalizedLogPartitionFunction_zero` constructs the local analytic logarithm
  through the branch satisfying `log 1 = 0`;
- `iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_formalCoeff` identifies
  analytic logarithmic derivatives with the formal logarithm coefficients;
- `iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude` gives the analytic
  connected-diagram formula.

Thus the formal machinery remains implementation infrastructure, while the analytic finite-mode
partition function and analytic connected-diagram theorem are the public endpoint.

## Fermionic capability matrix

| Capability | Status | Main result or module |
|---|---:|---|
| Algebraic Fock and CAR | done | `Fermionic.Algebra` |
| Free imaginary-time evolution | done | `Fermionic.ImaginaryTime` |
| Finite free Gibbs theory | done | `Fermionic.Thermal` |
| General finite-temperature pairing theorem | done | `Common/Thermal/BlochDeDominicis/Induction.lean` with fermionic instantiation |
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

## Bosonic line and convergence boundary

The bosonic line currently includes:

- occupation states `Mode →₀ ℕ`, algebraic Fock space, ladder operators, CCR, number operators, and
  grading under `Bosonic/Algebra/`;
- free diagonal and interaction-picture imaginary-time evolution;
- convergent free partition and particle-number series under explicit positivity assumptions;
- free two-point coefficients and a two-point Bloch–de Dominicis specialization;
- quartic interaction vertices, local-leg semantics, ordered diagram data, component decomposition,
  and componentwise scalar prefactors.

It does not yet expose a general perturbation umbrella. A finite set of bosonic modes has an infinite
occupation basis, so the finite-configuration operator integral used by the fermionic analytic line
cannot simply be specialized to bosons. A valid bosonic perturbation layer requires:

1. a summability-restricted arbitrary-operator Gibbs functional;
2. a locally finite, summability-controlled, or completed operator-integration interface;
3. compatible convergence hypotheses for Dyson coefficients and traces;
4. only then, reuse of the Common shuffle, cumulant, and connected-diagram infrastructure.

No finite-basis bosonic compatibility API should be introduced merely to mirror the fermionic module
tree.

## Work remaining for issue #345

The major entry-point, namespace, bosonic algebra-layout, and confirmed Dyson-wrapper migrations are
complete. The remaining refactor work is narrower:

1. continue auditing fermionic perturbation and diagrammatic declarations whose only content is
   parameter substitution into Common constructions;
2. remove statistic-encoded names only where namespace ownership already supplies the distinction;
3. regroup the long quartic Wick component stack only when a module boundary exposes proof internals
   rather than a reusable domain concept;
4. keep the analytic finite-mode partition function and analytic LCT as the public perturbative
   endpoint while demoting purely formal machinery to implementation modules where appropriate;
5. complete the breaking-name/import ledger and ensure every removed path is rejected by CI;
6. run repository-wide `lake build --wfail`, no-`sorry`, Theorem Catalog, and architecture checks
   before closing #345.

## Separate future research tracks

The following are not unfinished parts of the finite-mode fermionic analytic LCT:

- completed Hilbert-space representations of the Fock algebra;
- domains and functional calculus for unbounded Hamiltonians and ladder operators;
- infinite-mode or thermodynamic-limit partition functions;
- trace-class and Gibbs-state constructions beyond finite-dimensional SecondQuantization;
- time-ordered correlation functions and diagrams with external legs;
- a convergence-aware bosonic Dyson and linked-cluster theory.
