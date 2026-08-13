import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentGlobalCrossingParity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentOrderDecomposition

set_option linter.style.header false

/-!
# Quartic crossing parity compatibility import

The Statistics-generic quartic crossing-parity and pairing-weight factorization is owned by
`SecondQuantization.Common.Diagrammatics.Quartic.ComponentGlobalCrossingParity`.

This module currently remains only because the active two-point linked-cluster proof imports the
historical Fermionic path. It defines no Fermionic declarations. The Common order-decomposition
import preserves declarations that this historical path also supplied transitively to that proof.
Both compatibility imports should disappear once that consumer is migrated without changing its
mathematical route.
-/
