import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint

set_option linter.style.header false

/-!
# Statistics-independent diagrammatics

Quartic and two-point diagrammatics are organized as separate domain subtrees. The quartic subtree
owns quartic diagram syntax, connectivity, component restriction/reassembly, component-local
ordering/pairing, ordered-simplex bridges, and scalar factorization. The two-point subtree owns the
external-leg diagram syntax, full component partition/restriction/decomposition, canonical
external/vacuum splitting, componentwise products, interaction-time shuffles, and restricted-pair
transport/orientation.
-/
