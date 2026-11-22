import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.LinkedCluster.Analytic
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.LinkedCluster.Inversion

set_option linter.style.header false

/-!
# Fermionic linked-cluster diagrammatics

Canonical replica-based formal and analytic Dyson Linked Cluster Theorems, together with an
independent cumulant-inversion proof of the formal theorem. The first three formal-log coefficient identities follow by specializing
`Combinatorics.powerSeriesMomentCoeff_succ_recurrence`, without dedicated low-order
or fermionic wrapper theorems.
-/
