import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentPartition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointExternalConnectivity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointExternalRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointCanonicalComponentShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentPairProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointRestrictedPairEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointRestrictedPairOrientation

set_option linter.style.header false

/-!
# Statistics-independent diagrammatics

Quartic leg indexing, labelled quartic diagram syntax, connected-component restriction/reassembly and
component-decomposition equivalences; component-local orders, order-preserving shuffle decompositions,
component-local/global pairing compatibility and pair-product reindexing, shuffled ordered-simplex
integrands, and componentwise scalar factorization; two-point diagrams with distinguished external
legs, full component partitions, automatic connectivity of the two one-legged external vertices,
vacuum/external component restriction data, the canonical external-plus-vacuum decomposition of
component indices and interaction vertices, componentwise interaction-vertex products and Dyson
signs, order-preserving shuffles, local-time reconstruction, ordered-simplex products, normalized-pair
transport, and pair-orientation results.
-/
