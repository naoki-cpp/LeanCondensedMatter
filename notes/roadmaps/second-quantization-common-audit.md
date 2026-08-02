# Second Quantization Common — Structure and Extraction Audit

This note records the ownership boundary between statistics-independent second-quantization
infrastructure and the fermionic and bosonic physical APIs. It is a structural audit, not a claim
that the two statistics-specific developments must expose identical theorem sets.

## Public Common layout

`SecondQuantization.Common` has five responsibility-based areas:

| Import | Responsibility |
|---|---|
| `SecondQuantization.Common.Algebra` | Algebraic Fock spaces, statistics, grading, and the shared CAR/CCR interface. |
| `SecondQuantization.Common.ImaginaryTime` | Time ordering, diagonal evolution, interaction pictures, and KMS rotation. |
| `SecondQuantization.Common.Thermal` | Normalized functionals, diagonal traces, Gibbs infrastructure, and Bloch–de Dominicis. |
| `SecondQuantization.Common.Perturbation` | Finite-basis coefficientwise operator integration. |
| `SecondQuantization.Common.Diagrammatics` | Label-generic quartic diagrams and connected-component decomposition. |

`Common.Perturbation` is deliberately finite-basis infrastructure. It is not presented as a general
bosonic operator-integration layer.

## Extracted to general mathematics

### Normalized endomorphism functionals

`Analysis/NormalizedEndomorphismFunctional.lean` owns the general linear-algebra structure of a
linear functional on `Module.End` that maps the identity to `1`.

`Common.NormalizedOperatorFunctional Config` is the specialization to endomorphisms of
`AlgebraicFock Config`. Positivity, traces, Gibbs weights, and quasifree recursion remain separate
physics-facing properties.

### Products over finite partitions

`Combinatorics/FinpartitionProduct.lean` owns the statistics-independent product decomposition and
cardinality-power factorization results. Quartic-diagram component weights and Dyson signs specialize
those results rather than reproving them in SecondQuantization.

## Retained in Common

The following constructions are generic over statistics but remain second-quantization
infrastructure:

- `AlgebraicFock.lean`, including the occupation-basis and diagonal-operator vocabulary;
- `DiagonalEvolution.lean` and `InteractionPicture.lean`;
- `TimeOrdering.lean`, `ExchangeCommutator.lean`, and `ExchangeAlgebra.lean`;
- the fixed-four-leg `QuarticDiagram` combinatorics;
- `BlochDeDominicis/`, which combines pairing combinatorics, exchange statistics, operator
  functionals, and KMS hypotheses.

Moving these files unchanged into `Analysis` or `Combinatorics` would obscure their physical API
boundary rather than improve dependency ownership.

## Candidates for later general extraction

### Coefficientwise finite operator integration

`Common.FiniteOperatorIntegral` reconstructs an endomorphism of `AlgebraicFock Config` from
occupation-basis matrix coefficients. General extraction should wait for a genuinely reusable
finite-basis module or matrix-coordinate interface.

### Finsupp matrix-coordinate infrastructure

`matrixCoeff`, finite-support composition, diagonal operators, and extensionality may eventually be
factored through a general `Finsupp` linear-map layer. That would be an API redesign, not a file move.

## Statistics-specific specializations

A surviving declaration under `Fermionic` or `Bosonic` should provide at least one of the following:

- a statistic-specific operator, sign, occupation, energy, or convergence statement;
- a physics-facing name used by downstream theorems;
- an analytic hypothesis or proof that is not available from Common by parameter substitution alone.

Short files are not removed merely because they call Common lemmas. For example, physical Fock-space
abbreviations, CAR/CCR identities, free two-point results, and interaction-picture operators remain
useful public specializations.

Compatibility-only theorem wrappers and one-purpose files with no surviving physical use are removed
rather than retained for import compatibility.

## Final #345 audit results

The repository-wide audit after PR #425 found:

- no `Common` module importing `Fermionic` or `Bosonic`;
- no `Analysis` or `Combinatorics` module importing SecondQuantization;
- no remaining declaration names carrying obsolete `Fermion*`, `Fermionic*`, `Boson*`, or
  `Bosonic*` statistic suffixes in the physical source trees;
- no stale use of the removed fermionic ordered-diagram module;
- a set of short Common-heavy physical modules that were reviewed as specialization candidates.

The audit identified `Bosonic/Diagrammatics/QuarticLegFamily.lean` as an unused one-declaration public
module: its `quarticLegOperatorForSequence` declaration had no in-repository caller, and the file was
imported only by the Bosonic diagrammatics umbrella. It was removed together with the umbrella import.
A dedicated CI check rejects restoration of the deleted file or import path.

The remaining short modules contain physical definitions, statistic-specific proofs, or actively used
domain concepts. They are not classified as compatibility forwarding surfaces solely because their
proofs reuse Common results.

## Bosonic analytic boundary

The remaining Bosonic obstruction is analytic rather than organizational:

1. summability-aware trace cyclicity requires concrete operator classes and double-series estimates;
2. summability-aware KMS rotation requires Boltzmann-weight estimates and a clear operator domain;
3. a general bosonic Gibbs state and operator-valued Dyson integration require a completed Hilbert
   Fock space and convergence-aware bounded or unbounded operator infrastructure.

No false `[Fintype (Bosonic.Occupation Mode)]` assumption is introduced to imitate the finite
fermionic implementation.

## Physical source layout

The implementation and public responsibility layout now agree:

- `Common/{Algebra,ImaginaryTime,Thermal,Perturbation,Diagrammatics}/` owns shared constructions;
- `Fermionic/{Algebra,ImaginaryTime,Thermal,Perturbation,Diagrammatics}/` owns finite-mode fermionic
  specializations and the analytic Linked Cluster Theorem;
- `Bosonic/{Algebra,ImaginaryTime,Thermal,Diagrammatics}/` owns the convergence-aware bosonic line.

PR #351 removed the former `Bosonic/Foundations/` and `Bosonic/OperatorAlgebra/` split without
forwarding paths. The single public entry point remains:

```lean
import LeanCondensedMatter.SecondQuantization
```

### Bloch–de Dominicis layout

The statistics-independent framework is under `Common/Thermal/BlochDeDominicis/`:

- `Unnormalized/` contains operator and trace peel identities before normalization;
- `GibbsExpectation/` contains the normalized functional and two-/four-point recursion;
- `Induction.lean` contains the arbitrary-length pairing theorem;
- `PairingWeight.lean` contains the statistics-dependent crossing weight.

Concrete specializations are colocated with the physical thermal APIs that discharge their
hypotheses:

- `Bosonic/Thermal/BlochDeDominicis/TwoPoint.lean` supplies uncutoff summability proofs;
- `Fermionic/Thermal/BlochDeDominicis/TwoPoint.lean` supplies the finite-mode free two-point check;
- `Fermionic/Thermal/BlochDeDominicis/Examples/SingleMode.lean` records the algebraic four-point
  example.

This separation keeps the generic recursion independent of the statistics-specific analytic or
finite-basis verification.
