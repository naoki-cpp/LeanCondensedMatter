import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Pairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization

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
