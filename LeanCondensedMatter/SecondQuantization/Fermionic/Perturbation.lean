import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.FormalLogPartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.ContinuousDyson
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansionVerification
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment

set_option linter.style.header false

/-!
# Fermionic perturbation theory

Formal partition-function logarithms, finite-basis algebraic and continuous Dyson coefficients,
their verification, partition-series coefficients, and vertex moments. The continuous layer is a
thin specialization of the statistics-independent Common finite-configuration bridge.
-/
