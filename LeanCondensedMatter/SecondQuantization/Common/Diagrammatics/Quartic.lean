import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Connected
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentPartition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentConnected
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.Reassemble
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ReassembleLaws
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Pairing.ComponentPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Pairing.ComponentPairProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Pairing.FixedOrderComponentPair
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization.ComponentGlobalCrossingParity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization.ComponentEvaluation
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization.TwoPointLegEmbedding

set_option linter.style.header false

/-!
# Quartic diagram infrastructure

Statistics-independent quartic leg indexing, labelled diagram syntax, vertex ordering, connectivity,
connected-component restriction, reassembly and its inverse laws, component-decomposition equivalence
and generic connected-decomposition adapter, component-local orders and pairing compatibility,
fixed-global-order component-pair embeddings, componentwise scalar products, mixed two-point leg
embeddings, Statistics-generic crossing-parity/pairing-weight factorization, and the corresponding
scalar `Pairing.evaluation` factorization endpoint. Ordered-simplex shuffle analysis is consumed
directly from `Analysis/OrderedSimplex` by the fermionic amplitude layer.
-/
