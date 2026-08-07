import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.PairingEvaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing

set_option linter.style.header false

/-!
# Fermionic Dyson-to-diagram expansion

The implementation is split into operator/Dyson core, flattened-leg algebra, canonical density-state
pairing, its specialization of the shared generic pairing evaluator, and final Wick-diagram
reindexing modules. Each implementation module owns its explicit direct imports. Public theorems are
exposed through this entry point, while coordinate Gibbs-expectation calculations remain private
implementation machinery.
-/
