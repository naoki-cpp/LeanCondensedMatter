import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint

set_option linter.style.header false

/-!
# Statistics-independent diagrammatics

The quartic subtree owns zero-external-leg diagram syntax and component factorization.
`ExternalInsertion` owns the statistics-independent core syntax for an even finite family of
one-legged external insertions plus quartic interaction vertices, their external/vacuum component
split, and vacuum-component restriction to quartic diagrams. The established two-point subtree
retains its own representation and owns its component partition/restriction/decomposition, canonical
external/vacuum splitting, componentwise products, interaction-time shuffles, and restricted-pair
transport/orientation. A semantic bridge to the generic core is added only when a higher-point
consumer needs one.
-/
