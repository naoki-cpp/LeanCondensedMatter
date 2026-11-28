import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ReachableSupport
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteAnalyticBridge
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.QuarticDysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDyson
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExponential
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonPartitionFunction
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticLinkedCluster

set_option linter.style.header false

/-!
# Perturbation theory

Finite-support Dyson coefficients on arbitrary configuration types, quartic expansions,
and finite-dimensional analytic Dyson evolution, trace series, partition functions and
linked-cluster bridges. General norm estimates are provided by `Analysis.Dyson`.
-/
