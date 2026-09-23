import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.InteractionOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.ComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentShuffleParity

set_option linter.style.header false

/-!
# Statistics-independent external-insertion diagrammatics

This package provides the paired diagram core for an even finite family of one-legged external
insertions and quartic interaction vertices, the external-supported/vacuum connected-component
split, generic component restriction, restriction of vacuum components to ordinary quartic
diagrams, a component-local decomposition of normalized pairs, and an exact split of the global
crossing count into component-local and inter-component contributions. The core leg enumeration
places external insertions first and interaction legs afterward in increasing vertex/local-leg order,
providing the ordered basis for crossing/sign transport. Amplitude factorization remains downstream
work driven by concrete higher-point consumers.
-/
