# Second Quantization — Current Status

This page summarizes the current architecture and proved results in
`LeanCondensedMatter/SecondQuantization/`. The longer development narrative is in
[`second-quantization.md`](second-quantization.md), and the completed fermionic Linked Cluster Theorem
is documented in [`linked-cluster-theorem.md`](linked-cluster-theorem.md).

The source of truth for every completed claim is the referenced Lean declaration. The files described
as complete compile without `sorry`.

## Scope and architecture

The finite-mode fermionic line is the primary completed algebraic path. The bosonic line mirrors the
statistics-independent and algebraic layers where possible, but its thermal and Dyson layers require
summability-aware interfaces because a finite set of bosonic modes still has an infinite occupation
basis.

The current boundary is:

- finite-mode fermionic algebra, thermal theory, Dyson coefficients, Wick diagrams, and the
  coefficientwise Linked Cluster Theorem are implemented;
- the fermionic LCT is formal/algebraic and makes no perturbation-series convergence claim;
- the bosonic line has algebraic Fock, CCR, free thermal results, two-point Bloch–de Dominicis, and
  quartic diagram data, but not a general Dyson/LCT layer;
- completed-space unbounded-operator theory, trace-class theory, and thermodynamic limits remain
  separate tracks.

## Public import layout

| Area | Fermionic import | Bosonic import |
|---|---|---|
| Algebra | `SecondQuantization.Fermionic.Algebra` | `SecondQuantization.Bosonic.Algebra` |
| Imaginary time | `SecondQuantization.Fermionic.ImaginaryTime` | `SecondQuantization.Bosonic.ImaginaryTime` |
| Free thermal theory | `SecondQuantization.Fermionic.Thermal` | `SecondQuantization.Bosonic.Thermal` |
| Quartic diagrammatics | `SecondQuantization.Fermionic.Diagrammatics` | `SecondQuantization.Bosonic.Diagrammatics` |

The fermionic line additionally exports `SecondQuantization.Fermionic.Perturbation`, which contains
the finite-basis Dyson construction and formal partition-series logarithm.

`SecondQuantization.Fermionic` imports all five fermionic umbrellas. The final algebraic Dyson Linked
Cluster Theorem is exported through `SecondQuantization.Fermionic.Diagrammatics`, so it is also
available from the top-level Fermionic API.

## Shared statistics-independent layer

The dependency direction is one way: `Fermionic/` and `Bosonic/` may import `Common/`, while
`Common/` does not import a statistics-specific directory. General analysis and finite combinatorics
live in `Analysis/` and `Combinatorics/`.

| Area | Main modules | Current result |
|---|---|---|
| Algebraic Fock infrastructure | `Common/Algebra/` | Basis states, matrix coefficients, diagonal maps, grading, and exchange interfaces are generic in the configuration/statistics data. |
| Imaginary-time infrastructure | `Common/ImaginaryTime/` | Diagonal evolution, interaction-picture formulas, time-ordering primitives, and KMS rotation support both statistics. |
| Thermal functionals | `Analysis/NormalizedEndomorphismFunctional.lean`, `Common/Thermal/` | Normalized functionals, finite weighted traces, Gibbs infrastructure, and the abstract Bloch–de Dominicis theorem. |
| Finite operator integration | `Common/Perturbation/FiniteOperatorIntegral.lean` | Coefficientwise operator integration for finite configuration types. |
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
- genuine finite-basis Dyson coefficients, normalized partition coefficients, and a formal Dyson
  partition series;
- a general non-diagonal quartic interaction and local-leg semantics;
- ordered quartic Wick diagrams, full amplitudes, and the Dyson diagram expansion;
- component decomposition, component-order/shuffle calculus, fermionic pairing compatibility, and
  full amplitude factorization;
- a concrete weighted-diagram family and the connected-diagram formula for Dyson vertex cumulants;
- the general formal-log/finite-set-cumulant bridge;
- the final algebraic Dyson Linked Cluster Theorem.

## Fermionic LCT milestones

| Milestone | Deliverable | Status |
|---|---|---|
| M0 | Statistics-independent component-shuffle product calculus | complete through PR #247 |
| M1 | Fermionic contraction-integrand factorization | complete through PR #256; cleanup through PR #282 |
| M2 | Full quartic Wick-amplitude factorization | complete in PR #287 |
| M3 | Connected-diagram formula for `dysonVertexCumulant` | complete in PR #291 |
| M4 | General finite-set cumulant / formal-`log` EGF bridge | complete in PR #295 |
| M5 | Final Dyson LCT theorem and Fermionic API export | complete in PR #299 |

The final theorem is

```lean
factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

and states, for `n ≠ 0`,

```text
n! [λⁿ] log(normalized Dyson partition series)
  = ∑ connected n-vertex quartic Wick diagrams, amplitude(diagram).
```

The proof chain is:

1. global orders decompose into component-local orders and component shuffles;
2. contraction integrands factor over connected components;
3. complete quartic Wick amplitudes factor over connected components;
4. the abstract weighted-diagram theorem identifies finite-set cumulants with connected diagrams;
5. factorial-normalized formal-log coefficients are finite-set cumulants;
6. the normalized Dyson coefficient is exactly the Dyson vertex moment coefficient.

## Fermionic capability matrix

| Capability | Status | Main result or module |
|---|---:|---|
| Algebraic Fock and CAR | done | `Fermionic.Algebra` |
| Free imaginary-time evolution | done | `Fermionic.ImaginaryTime` |
| Finite free Gibbs theory | done | `Fermionic.Thermal` |
| General finite-temperature pairing theorem | done | `Common/Thermal/BlochDeDominicis/Induction.lean` with fermionic instantiation |
| Dyson coefficients and partition series | done | `Fermionic/Perturbation/DysonExpansion.lean`, `DysonPartitionSeries.lean` |
| Full quartic Wick amplitude | done | `Fermionic/Diagrammatics/WickDiagram/Amplitude.lean` |
| Dyson diagram expansion | done | `Fermionic/Diagrammatics/DysonDiagramExpansion.lean` |
| Full amplitude factorization | done | `WickDiagram/AmplitudeFactorization.lean` |
| Connected-diagram cumulant theorem | done | `DysonConnectedDiagramExpansion.lean` |
| Formal-log coefficient bridge | done | `Combinatorics/PowerSeriesCumulant.lean` |
| Algebraic Dyson LCT | done | `DysonLinkedClusterTheorem.lean` |
| Analytic equality with `Tr exp(-β(H₀+λV))` | pending | requires a separate analytic/convergence argument |

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
| Dyson Linked Cluster Theorem | done, formal/algebraic | pending | Bosonic analytic and Dyson layers remain. |

## Analytic blockers

### Bosonic operator integration

`Common/Perturbation/FiniteOperatorIntegral.lean` reconstructs operators using a finite sum over output
basis states and therefore requires a finite configuration type. A bosonic replacement needs a locally
finite, summability-controlled, or completed operator class.

### Bosonic Gibbs expectations

The existing bosonic thermal results establish summability for specific expressions. A reusable
arbitrary-operator functional must encode sufficient summability hypotheses in its type or theorem
statements.

### Analytic fermionic partition function

The proved fermionic LCT concerns the formal series assembled from Dyson coefficients. A further
finite-dimensional analytic theorem should identify that series with the Taylor expansion of

```text
Tr(exp(-β(H₀ + λV))) / Tr(exp(-βH₀)).
```

### Completed-space operator theory

Hilbert-space completion, domains of unbounded ladder operators, trace-class theory, and infinite-mode
limits remain outside the algebraic SecondQuantization layer unless a theorem explicitly introduces
the required analytic hypotheses.

## Recommended next order

1. add explicit `n = 1, 2, 3` coefficient and connected-diagram regression theorems;
2. prove the finite-dimensional analytic Dyson evolution identity and identify the formal partition
   series with the Taylor expansion of the interacting partition function;
3. extend connectedness to time-ordered correlation functions and diagrams with external legs;
4. design a summability-restricted bosonic Gibbs functional;
5. introduce a compatible bosonic operator-integral/Dyson interface;
6. reuse the Common component-shuffle, cumulant, and connectedness infrastructure for the bosonic
   line once its analytic hypotheses are available.
