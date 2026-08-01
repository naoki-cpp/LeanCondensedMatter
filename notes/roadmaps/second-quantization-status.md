# Second Quantization — Current Status

This page summarizes the current architecture and proved results in
`LeanCondensedMatter/SecondQuantization/`. The longer development narrative is in
[`second-quantization.md`](second-quantization.md), the completed fermionic Linked Cluster Theorem is
documented in [`linked-cluster-theorem.md`](linked-cluster-theorem.md), and the breaking canonical-API
migration is tracked in [`second-quantization-refactor.md`](second-quantization-refactor.md).

The source of truth for every completed claim is the referenced Lean declaration. The files described
as complete compile without `sorry`.

## Scope and architecture

The finite-mode fermionic line is the primary completed path. It now includes both the
formal/algebraic Dyson Linked Cluster Theorem and the finite-dimensional analytic theorem for the
genuine interacting partition function. The bosonic line mirrors the statistics-independent and
algebraic layers where possible, but its thermal and Dyson layers require summability-aware interfaces
because a finite set of bosonic modes still has an infinite occupation basis.

The current boundary is:

- algebraic Fock, diagonal evolution, interaction-picture coefficient formulas, the Heisenberg
  semigroup law, and fermionic quartic local-leg identities are generic beyond finite mode sets when
  no full-basis trace or enumeration is used;
- finite-mode fermionic Gibbs theory, Dyson coefficients, Wick diagrams, the formal LCT, the analytic
  partition-function identity, and the analytic LCT are implemented;
- the bosonic line has algebraic Fock, CCR, free thermal results, two-point Bloch–de Dominicis, and
  quartic diagram data, but not a general Dyson/LCT layer;
- completed-space unbounded-operator theory, trace-class theory, infinite-mode limits, and
  thermodynamic limits remain separate tracks.

## Public import layout

The single full public entry point is

```lean
import LeanCondensedMatter.SecondQuantization
```

Responsibility-specific code may import a leaf umbrella directly:

| Area | Fermionic import | Bosonic import |
|---|---|---|
| Algebra | `LeanCondensedMatter.SecondQuantization.Fermionic.Algebra` | `LeanCondensedMatter.SecondQuantization.Bosonic.Algebra` |
| Imaginary time | `LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime` | `LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime` |
| Free thermal theory | `LeanCondensedMatter.SecondQuantization.Fermionic.Thermal` | `LeanCondensedMatter.SecondQuantization.Bosonic.Thermal` |
| Perturbation theory | `LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation` | not yet exposed |
| Quartic diagrammatics | `LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics` | `LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics` |

The former exact umbrella modules `LeanCondensedMatter.SecondQuantization.Common`, `.Fermionic`, and
`.Bosonic` are intentionally removed. The top-level `LeanCondensedMatter.SecondQuantization` module
imports the canonical Common, Fermionic, and Bosonic leaf umbrellas.

## Finiteness boundary

Finite mode assumptions should appear only where the implementation genuinely needs a finite global
basis or finite enumeration.

Currently finite-mode or finite-configuration:

- finite weighted traces, Gibbs expectations, and free partition functions;
- finite operator integration and reconstruction;
- the fermionic Dyson partition series and diagram sums;
- the finite-dimensional analytic partition function and analytic LCT;
- enumeration of all quartic vertex labels or diagrams.

Currently generic in the mode/configuration type where the surrounding algebra is available:

- algebraic Fock vectors and matrix coefficients;
- diagonal and interaction-picture coefficient formulas;
- `Common.heisenbergEvolve_heisenbergEvolve`;
- fermionic interaction-picture basic API;
- fermionic quartic local-leg algebra and time evolution.

For bosons, `Bosonic.Occupation Mode = Mode →₀ ℕ` is infinite even when `Mode` is finite. A false
`[Fintype (Bosonic.Occupation Mode)]` assumption is not an acceptable substitute for the missing
summability-aware interfaces.

## Shared statistics-independent layer

The dependency direction is one way: `Fermionic/` and `Bosonic/` may import `Common/`, while
`Common/` does not import a statistics-specific directory. General analysis and finite combinatorics
live in `Analysis/` and `Combinatorics/`.

| Area | Main modules | Current result |
|---|---|---|
| Algebraic Fock infrastructure | `Common/Algebra/` | Basis states, matrix coefficients, diagonal maps, grading, and exchange interfaces are generic in the configuration/statistics data. |
| Imaginary-time infrastructure | `Common/ImaginaryTime/` | Diagonal evolution, interaction-picture formulas, time-ordering primitives, and KMS rotation support both statistics; several coefficient and semigroup results are valid without global finiteness. |
| Thermal functionals | `Analysis/NormalizedEndomorphismFunctional.lean`, `Common/Thermal/` | Normalized functionals, finite weighted traces, Gibbs infrastructure, and the abstract Bloch–de Dominicis theorem. |
| Finite operator integration | `Common/Perturbation/FiniteOperatorIntegral.lean` | Coefficientwise operator integration for finite configuration types. |
| Continuous and analytic Dyson theory | `Common/Perturbation/AnalyticDyson*.lean` | Norm-convergent finite-dimensional Dyson evolution, Volterra/exponential identities, trace coefficients, and Taylor-series control. |
| Quartic diagrams | `Common/Diagrammatics/`, `Combinatorics/FinpartitionProduct.lean` | Labels, ordered data, connectedness, component restriction/reassembly, decomposition equivalence, and component-local orders. |
| Ordered-simplex shuffle calculus | `Analysis/BinaryShuffleSlotOrderedSimplex.lean`, `Analysis/FamilyShuffleOrderedSimplex.lean`, `Common/Diagrammatics/ComponentOrderedSimplexProduct.lean` | Binary and finite-family shuffle sums equal products of local ordered-simplex integrals. |
| Moment/cumulant and diagram connectedness | `Combinatorics/MomentCumulant.lean`, `Combinatorics/DiagramConnectedness.lean` | Finite-set moment–cumulant inversion and the abstract weighted-diagram connectedness theorem. |
| Formal-log bridge | `Combinatorics/PowerSeriesCumulant.lean` | Factorial-normalized `log` coefficients equal finite-set cumulants for arbitrary normalized complex power series. |

## Fermionic line

The finite-mode fermionic line currently includes:

- occupation-number Fock space, creation/annihilation operators, CAR, grading, and Hamiltonians;
- free imaginary-time evolution and arbitrary interaction-picture matrix coefficients;
- finite-basis Gibbs weights, free partition and two-point functions, contractions, KMS rotation, and
  the finite-temperature Bloch–de Dominicis pairing theorem;
- Common-owned finite-basis Dyson coefficients, fermionic normalized partition coefficients, and a
  formal Dyson partition series;
- a general non-diagonal quartic interaction and local-leg semantics;
- ordered quartic Wick diagrams, full amplitudes, and the Dyson diagram expansion;
- component decomposition, component-order/shuffle calculus, fermionic pairing compatibility, and
  full amplitude factorization;
- a concrete weighted-diagram family and the connected-diagram formula for Dyson vertex cumulants;
- the general formal-log/finite-set-cumulant bridge;
- the final formal/algebraic Dyson Linked Cluster Theorem;
- the norm-convergent analytic Dyson partition function and its Taylor series;
- the local analytic normalized logarithm and the analytic connected-diagram theorem.

## Fermionic LCT milestones

| Milestone | Deliverable | Status |
|---|---|---|
| M0 | Statistics-independent component-shuffle product calculus | complete through PR #247 |
| M1 | Fermionic contraction-integrand factorization | complete through PR #256; cleanup through PR #282 |
| M2 | Full quartic Wick-amplitude factorization | complete in PR #287 |
| M3 | Connected-diagram formula for `dysonVertexCumulant` | complete in PR #291 |
| M4 | General finite-set cumulant / formal-`log` EGF bridge | complete in PR #295 |
| M5 | Final formal Dyson LCT theorem | complete in PR #299 |
| A0 | Analytic Dyson partition-function and analytic LCT bridge | complete |

The formal theorem is

```lean
SecondQuantization.Fermionic.
  factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

and states, for `n ≠ 0`,

```text
n! [λⁿ] log(normalized Dyson partition series)
  = ∑ connected n-vertex quartic Wick diagrams, amplitude(diagram).
```

The analytic endpoint is

```lean
SecondQuantization.Fermionic.
  iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude
```

and states schematically

```text
(dⁿ/dλⁿ)|₀ log(Tr exp(-β(H₀ + λV)) / Tr exp(-βH₀))
  = ∑ connected n-vertex quartic Wick diagrams, amplitude(diagram).
```

The proof chain is:

1. global orders decompose into component-local orders and component shuffles;
2. contraction integrands factor over connected components;
3. complete quartic Wick amplitudes factor over connected components;
4. the abstract weighted-diagram theorem identifies finite-set cumulants with connected diagrams;
5. factorial-normalized formal-log coefficients are finite-set cumulants;
6. the normalized Dyson coefficient is exactly the Dyson vertex moment coefficient;
7. the finite-dimensional Dyson trace series sums to the interacting partition function;
8. analytic Taylor uniqueness and the logarithmic recurrence identify analytic derivatives with the
   formal cumulant coefficients.

## Fermionic capability matrix

| Capability | Status | Main result or module |
|---|---:|---|
| Algebraic Fock and CAR | done | `Fermionic.Algebra` |
| Free imaginary-time evolution | done | `Fermionic.ImaginaryTime` |
| Generic Heisenberg/interaction-picture coefficient laws | done | `Common/ImaginaryTime/DiagonalEvolution.lean`, `Common/ImaginaryTime/InteractionPicture.lean` |
| Finite free Gibbs theory | done | `Fermionic.Thermal` |
| General finite-temperature pairing theorem | done | `Common/Thermal/BlochDeDominicis/Induction.lean` with fermionic instantiation |
| Dyson coefficients | done | `Common.dysonCoeff` and `Common/Perturbation/` |
| Fermionic partition series | done | `Fermionic/Perturbation/DysonPartitionSeries.lean` |
| Full quartic Wick amplitude | done | `Fermionic/Diagrammatics/WickDiagram/Amplitude.lean` |
| Dyson diagram expansion | done | `Fermionic/Diagrammatics/DysonDiagramExpansion.lean` |
| Full amplitude factorization | done | `WickDiagram/AmplitudeFactorization.lean` |
| Connected-diagram cumulant theorem | done | `DysonConnectedDiagramExpansion.lean` |
| Formal-log coefficient bridge | done | `Combinatorics/PowerSeriesCumulant.lean` |
| Formal/algebraic Dyson LCT | done | `DysonLinkedClusterTheorem.lean` |
| Analytic equality with `Tr exp(-β(H₀+λV))` | done | `AnalyticDysonPartitionFunction.lean` |
| Analytic normalized-log LCT | done | `AnalyticLinkedClusterIdentification.lean` |
| Low-order `n = 1,2,3` regression corollaries | pending | follow-up phase F1 |
| Correlation functions with external legs | pending | follow-up phase F3 |

## Bosonic line

The bosonic line currently includes:

- occupation states `Mode →₀ ℕ`, algebraic Fock space, ladder operators, CCR, number operators, and
  grading;
- free diagonal and interaction-picture imaginary-time evolution;
- convergent free partition and particle-number series under explicit positivity assumptions;
- free two-point coefficients and an uncutoff two-point Bloch–de Dominicis specialization;
- quartic interaction vertices, local-leg CCR semantics, ordered diagram data, component
  decomposition, and componentwise scalar prefactors.

The bosonic line does not yet include a general arbitrary-operator Gibbs functional, a compatible
Dyson coefficient construction, the full quartic Wick amplitude, or a Dyson diagram expansion.

## Fermion/boson parity matrix

| Capability | Fermionic | Bosonic | Reason for a gap |
|---|---:|---:|---|
| Algebraic Fock and ladder operators | done | done | — |
| CAR/CCR through Common exchange algebra | done | done | — |
| Free imaginary-time evolution | done | done | — |
| Algebraic interaction picture | done | done | — |
| Free thermal two-point result | done | done | Bosonic proof carries explicit summability assumptions. |
| General finite-temperature pairing theorem | done | instantiated at two point | Arbitrary bosonic Gibbs functionals need a convergence-aware domain. |
| Quartic local-leg and ordered-diagram data | done | done | — |
| Component decomposition equivalence | done | done | Shared through Common. |
| Component-shuffle ordered-simplex product | done | reusable | Statistics independent. |
| Full quartic Wick amplitude | done | pending | Bosonic expectation/contraction layer is incomplete. |
| Dyson diagram expansion | done | pending | Bosonic Dyson coefficients are incomplete. |
| Full amplitude factorization | done | pending | Depends on the full bosonic amplitude. |
| Connected-diagram finite-set cumulant theorem | done | abstract machinery reusable | Needs a bosonic weighted-diagram instance. |
| Formal-log coefficient bridge | done and statistics independent | reusable | Already lives in `Combinatorics/`. |
| Dyson Linked Cluster Theorem | done, formal and analytic finite-mode | pending | Bosonic analytic and Dyson layers remain. |

## Remaining analytic blockers

### Bosonic operator integration

`Common/Perturbation/FiniteOperatorIntegral.lean` reconstructs operators using a finite sum over output
basis states and therefore requires a finite configuration type. A bosonic replacement needs a locally
finite, summability-controlled, or completed operator class.

### Bosonic Gibbs expectations

The existing bosonic thermal results establish summability for specific expressions. A reusable
arbitrary-operator functional must encode sufficient summability hypotheses in its type or theorem
statements.

### Completed-space operator theory

The completed fermionic analytic theorem is finite-dimensional. Hilbert-space completion, domains of
unbounded ladder operators, trace-class theory, infinite-mode limits, and thermodynamic limits remain
outside the algebraic SecondQuantization layer unless a theorem explicitly introduces the required
analytic hypotheses.

## Canonical-API refactor status

Issue #345 is reorganizing SecondQuantization around canonical ownership rather than compatibility
aliases or statistic-encoded names. The single entry point, namespace ownership, fermionic core names,
bosonic algebra layout, and principal Common Dyson ownership migrations are complete. Remaining work
continues the thin-wrapper audit, consolidates perturbation and diagrammatic public endpoints around
the analytic finite-mode result, and completes migration documentation and validation.

See [`second-quantization-refactor.md`](second-quantization-refactor.md) for the detailed migration map.

## Recommended next order

1. finish the remaining canonical-API wrapper and public-endpoint consolidation tracked by #345;
2. add explicit `n = 1, 2, 3` coefficient and connected-diagram regression theorems;
3. extend connectedness to time-ordered correlation functions and diagrams with external legs;
4. design a summability-restricted bosonic Gibbs functional;
5. introduce a compatible bosonic operator-integral/Dyson interface;
6. reuse the Common component-shuffle, cumulant, and connectedness infrastructure for the bosonic
   line once its analytic hypotheses are available;
7. treat completed-space, infinite-mode, and thermodynamic-limit results as separate analytic tracks.
