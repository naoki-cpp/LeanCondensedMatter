import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Determinant
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing

set_option linter.style.header false

/-!
# Fermionic Dyson-to-diagram expansion

The implementation is split into operator/Dyson core, flattened-leg algebra, canonical pairing
evaluation through the free Gibbs density state, the determinant form of the free quartic Wick
expansion, and final Wick-diagram reindexing modules. Each implementation module owns its explicit
direct imports. Public theorems are exposed through this entry point, while finite Gibbs coordinate
calculations remain private implementation machinery.
-/
