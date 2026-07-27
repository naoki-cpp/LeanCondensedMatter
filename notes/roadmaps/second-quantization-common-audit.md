# Second Quantization Common — Structure and Extraction Audit

This note records which declarations belong in statistics-independent second quantization, which are
more general mathematical facts, and which Common results may later become essentially free Bosonic
API.  It is a structural audit, not a claim that the fermionic and bosonic developments must have
identical files or theorem sets.

## Public Common layout

`SecondQuantization.Common` imports five responsibility-based umbrellas:

| Import | Responsibility |
|---|---|
| `SecondQuantization.Common.Algebra` | Algebraic Fock spaces, statistics, grading, and the shared CAR/CCR interface. |
| `SecondQuantization.Common.ImaginaryTime` | Time ordering, diagonal evolution, interaction pictures, and KMS rotation. |
| `SecondQuantization.Common.Thermal` | Normalized functionals, diagonal traces, Gibbs infrastructure, and Bloch–de Dominicis. |
| `SecondQuantization.Common.Perturbation` | Finite-basis coefficientwise operator integration. |
| `SecondQuantization.Common.Diagrammatics` | Label-generic quartic diagrams and connected-component decomposition. |

The categories align with the statistics-specific umbrellas where their responsibilities match.
`Common.Perturbation` is intentionally marked as finite-basis infrastructure rather than presented as
an already-shared Bosonic layer.

## Extracted to general mathematics

### Normalized endomorphism functionals

`Analysis/NormalizedEndomorphismFunctional.lean` now defines the general linear-algebra structure of
a linear functional on `Module.End` that maps the identity to `1`.

`Common.NormalizedOperatorFunctional Config` is only the specialization to endomorphisms of
`AlgebraicFock Config`.  Positivity, traces, Gibbs weights, and quasifree recursion remain separate
physics-facing properties.

### Products over finite partitions

`Combinatorics/FinpartitionProduct.lean` now contains:

- decomposition of a product over a finite set into iterated products over partition parts;
- factorization of `a ^ s.card` into powers indexed by the cardinalities of the parts.

The quartic-diagram component-weight and Dyson-sign theorems now specialize those general facts rather
than reproving them inside `SecondQuantization.Common`.

## Retained in Common

The following files are generic over statistics but remain second-quantization infrastructure:

- `AlgebraicFock.lean`: mathematically a free complex vector space, but its public names and diagonal
  operator API are the central basis representation used throughout the physical development.
- `DiagonalEvolution.lean` and `InteractionPicture.lean`: algebraic rather than analytic operator
  exponentials, but specifically organized around the occupation-basis/Fock-space representation.
- `TimeOrdering.lean`, `ExchangeCommutator.lean`, and `ExchangeAlgebra.lean`: explicitly depend on the
  particle-statistics parameter.
- `QuarticDiagram*.lean`: label-generic combinatorics, but the fixed four-leg vertex model is a
  second-quantization diagram object rather than a general graph or partition theorem.
- `BlochDeDominicis/`: combines perfect-pairing combinatorics with exchange statistics, operator
  functionals, and KMS hypotheses.

## Candidates for later general extraction

### Coefficientwise finite operator integration

`Common.FiniteOperatorIntegral` is analytically flavored, but its current definition reconstructs an
endomorphism specifically on `AlgebraicFock Config` from occupation-basis matrix coefficients.  Moving
it to `Analysis/` should wait for a genuinely general finite-basis module or matrix-coordinate
interface; moving the current file unchanged would reverse the intended dependency direction.

### Finsupp matrix-coordinate infrastructure

`matrixCoeff`, finite-support composition, diagonal operators, and extensionality could eventually be
factored through a general `Finsupp` linear-map module.  This would be a larger API redesign, not a
simple file move, because these names currently define the algebraic-Fock vocabulary used throughout
SecondQuantization.

## Bosonic specializations already exposed

The statistics-independent improvements identified by the original audit have now produced thin
Bosonic API where no new convergence argument is needed:

1. **Interaction-picture regularity.**
   `Bosonic.matrixCoeff_interactionPicture`, its continuity theorem, and its interval-integrability
   theorem directly specialize the Common finite-support proof; no finite configuration type is
   assumed.
2. **Algebraic free-evolution and quartic formulas.**
   The Bosonic API exposes Heisenberg-evolution composition together with interaction-picture formulas
   for quartic vertices and finite quartic interactions.
3. **Exchange and particle-number bridges.**
   The ordinary bosonic commutator is connected to `Common.exchangeCommutator`, and same-charge
   two-ladder diagonal coefficients vanish by the Common particle-number selection rule.

These additions are API specializations rather than duplicated proofs. They do not construct a
general bosonic Gibbs functional or a bosonic Dyson integral.

## Remaining nearly-free Bosonic candidates

1. **Summability-aware trace cyclicity.**
   `Common.tsumTrace_comp_comm` and related lemmas apply to arbitrary configuration types once the
   required double-series summability is supplied. Concrete Bosonic results should prove those
   hypotheses for a useful operator class rather than recreate the algebraic proof.
2. **Summability-aware KMS rotation.**
   The `tsumTrace` KMS path is already generic under explicit summability hypotheses. A public
   Bosonic theorem still needs the relevant Boltzmann-weight estimates and a clear operator domain.
3. **Additional quartic component aliases.**
   Common restriction, reassembly, decomposition, vertex-product, and sign-factorization results are
   statistics independent. New Bosonic names are worthwhile only where they make the public API
   easier to use; the proofs should remain in Common.

The main remaining Bosonic obstruction is analytic: arbitrary Gibbs expectations and operator-valued
Dyson integration need a convergence-aware domain. Algebraic and finite-support results should remain
independent of that larger construction.

## Physical source layout

The public responsibility umbrellas and physical source layout now agree wherever the internal
mathematics has the same boundary:

- `Common/{Algebra,ImaginaryTime,Thermal,Perturbation,Diagrammatics}/` contains the shared
  statistics-independent implementations;
- `Fermionic/{Algebra,ImaginaryTime,Thermal,Perturbation,Diagrammatics}/` contains the finite-mode
  fermionic implementations, with `QuantumLinkedCluster` classified under `Thermal/`;
- `Bosonic/{ImaginaryTime,Thermal,Diagrammatics}/` follows the same responsibility names, while the
  algebraic implementation intentionally keeps the finer `Foundations/` and `OperatorAlgebra/`
  split behind the public `Bosonic.Algebra` umbrella.

No compatibility shims remain at the former flat Common or Fermionic implementation paths. The
statistics-specific Bloch–de Dominicis specializations now live under each statistics' `Thermal/`
directory. Bosonic plain-namespace occupation/Fock aliases still exist as compatibility API, but
internal Bosonic code uses the canonical `SecondQuantization.Bosonic` names.

### Bloch–de Dominicis layout

The statistics-independent framework is under `Common/Thermal/BlochDeDominicis/` and is split by
mathematical role:

- `Unnormalized/` contains operator and trace peel identities before normalization;
- `GibbsExpectation/` contains the normalized functional and two-/four-point recursion;
- `Induction.lean` contains the arbitrary-length pairing theorem;
- `PairingWeight.lean` contains the statistics-dependent crossing weight.

Concrete specializations are colocated with the thermal APIs that discharge their hypotheses:

- `Bosonic/Thermal/BlochDeDominicis/TwoPoint.lean` supplies the uncutoff summability proof;
- `Fermionic/Thermal/BlochDeDominicis/TwoPoint.lean` supplies the finite-mode free two-point check;
- `Fermionic/Thermal/BlochDeDominicis/Examples/SingleMode.lean` records the algebraic four-point
  example for a normalized diagonal weight.

This separates the general recursion mechanism from the statistics-specific analytic or finite-basis
verification without pretending that the two concrete thermal theories have identical assumptions.
