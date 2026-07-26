import LeanCondensedMatter.SecondQuantization.Common.OneParticleSpace
import LeanCondensedMatter.SecondQuantization.Common.Statistics
import LeanCondensedMatter.SecondQuantization.Common.OccupationBasis
import LeanCondensedMatter.SecondQuantization.Common.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.FiniteOperatorIntegral
import LeanCondensedMatter.SecondQuantization.Common.ParticleNumberSelectionRule
import LeanCondensedMatter.SecondQuantization.Common.ExchangeCommutator
import LeanCondensedMatter.SecondQuantization.Common.ExchangeAlgebra
import LeanCondensedMatter.SecondQuantization.Common.TimeOrdering
import LeanCondensedMatter.SecondQuantization.Common.DiagonalEvolution
import LeanCondensedMatter.SecondQuantization.Common.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Common.NormalizedOperatorFunctional
import LeanCondensedMatter.SecondQuantization.Common.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.KMSRotation
import LeanCondensedMatter.SecondQuantization.Common.QuarticVertexLabel
import LeanCondensedMatter.SecondQuantization.Common.QuarticLeg
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagram
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramOrdered
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramConnected
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramComponentPartition
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramComponentConnected
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramReassemble
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramReassembleComponentPartitionEq
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramReassembleRestrictComponent
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramReassembleDecompose
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis

set_option linter.style.header false
/-!
# Statistics-independent second quantization

Umbrella module for infrastructure shared by the fermionic and bosonic lines.

The shared layer is organized into four groups:

1. **Algebraic Fock infrastructure:** occupation-basis interfaces, algebraic Fock spaces, matrix
   coefficients, diagonal operators, grading selection rules, and finite-basis operator integrals.
2. **Evolution and exchange algebra:** statistics, `ζ`-commutators, CAR/CCR interfaces, imaginary-time
   ordering, diagonal evolution, the algebraic interaction picture, KMS rotation, and normalized
   operator functionals.
3. **Quartic diagram combinatorics:** vertex labels, leg indexing, ordered data, connectedness,
   component restriction/reassembly, decomposition equivalences, and componentwise scalar products.
4. **Bloch–de Dominicis infrastructure:** pairing weights and the abstract finite-temperature pairing
   expansion.

`Common/` contains no import of `Fermionic/` or `Bosonic/`; statistics-specific modules instantiate
these APIs. Some declarations, notably finite operator integration and the current closed formula for
interaction-picture matrix coefficients, still require a finite configuration type. Bosonic modules
therefore use only the unrestricted algebraic part unless separate summability results are supplied.
-/
