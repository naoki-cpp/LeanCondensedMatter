import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.InteractionOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.ComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentEvaluation
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentShuffleParity

set_option linter.style.header false

/-!
# Statistics-independent external-insertion diagrammatics

This package describes paired diagrams formed from an even finite family of one-legged external
insertions and quartic interaction vertices. It provides the external-supported/vacuum
connected-component split, component restriction, restriction of vacuum components to ordinary
quartic diagrams, component-local decomposition of normalized pairs, and the exact decomposition of
the global crossing count into component-local and inter-component contributions.

The canonical leg enumeration places external insertions first and interaction legs afterward in
increasing vertex and local-leg order. The package is purely combinatorial: concrete operator
amplitudes and statistics-specific ordering signs are supplied separately.
-/
