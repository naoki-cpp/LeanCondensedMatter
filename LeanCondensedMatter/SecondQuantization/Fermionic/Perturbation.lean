import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.FormalLogPartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansionVerification
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment

set_option linter.style.header false

/-!
# Fermionic perturbation theory

Formal partition-function logarithms, finite-basis Dyson coefficients and their verification,
partition-series coefficients, and vertex moments. This layer has no current bosonic counterpart
because the bosonic occupation basis requires a convergence-aware operator-integral interface.
-/
