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

## Bosonic results that may later be nearly free

No Bosonic files are changed by this audit.  The following Common results or proof improvements are
likely to support later thin Bosonic specializations:

1. **Interaction-picture matrix coefficients without a finite configuration type.**
   `Common.matrixCoeff_interactionPicture`, its continuity theorem, and its interval-integrability
   theorem now use only finite support of algebraic-Fock vectors.  A later Bosonic PR can expose the
   corresponding theorems without adding convergence assumptions.
2. **Summability-aware trace cyclicity.**
   `Common.tsumTrace_comp_comm` and the related summability lemmas already apply to an arbitrary
   configuration type once the required double-series summability is supplied.  Bosonic work should
   prove those hypotheses for the intended operator class rather than recreate the algebraic proof.
3. **Summability-aware KMS rotation.**
   The `tsumTrace` KMS-rotation path in `Common.KMSRotation` is already formulated for infinite
   configuration types under explicit summability hypotheses.  Free Bosonic aliases should follow
   only after the concrete Boltzmann-weight hypotheses are connected.
4. **Particle-number selection rules.**
   `Common.ParticleNumberSelectionRule` can yield Bosonic vanishing statements whenever the relevant
   charge-shift hypotheses are available; these should be specialized only where they improve the
   public Bosonic API.
5. **Quartic component identities.**
   Common connected-component restriction, reassembly, decomposition, vertex-product, and sign
   factorization are already statistics independent.  Future Bosonic additions should normally be
   thin names or direct uses, not duplicated proofs.

The main remaining Bosonic obstruction is still analytic: arbitrary Gibbs expectations and
operator-valued Dyson integration need a convergence-aware domain.  The algebraic and finite-support
results above should not be blocked on that larger construction.
