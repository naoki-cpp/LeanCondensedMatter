import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing

set_option linter.style.header false

/-!
# Fermionic Dyson-to-diagram expansion

The implementation is split into operator/Dyson core, flattened-leg algebra, canonical density-state
pairing, and final Wick-diagram reindexing modules. Each implementation module owns its direct
imports, while public theorems are exposed through this entry point; coordinate Gibbs-expectation
calculations remain private proof machinery.
-/
