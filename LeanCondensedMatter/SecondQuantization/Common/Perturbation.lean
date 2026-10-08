import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteSupportIntegral
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ReachableSupport
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteAnalyticBridge
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonOperatorIntegral
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.QuarticDysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDyson
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExponential
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceMoment
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonTrace
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonPartitionFunction
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticLinkedCluster

set_option linter.style.header false

/-!
# Perturbative infrastructure

The public layer includes finite reachable supports, finite-support coefficientwise integration, and
a single finite-order Dyson coefficient construction valid for arbitrary configuration types,
together with direct matrix-coefficient continuity. Statistics-independent
quartic Dyson helpers package the canonical scalar time factors and fixed-sequence coefficients used
by particle-specific finite-support expansions. On finite configuration types, that canonical recursion
also satisfies the coefficientwise reconstructed
operator-integral equation used by the continuous finite-dimensional realization.

The analytic evolution, trace series, and exponential identities remain finite-basis constructions
and retain their explicit finiteness assumptions; generic Dyson norm bounds live in `Analysis.Dyson`.
-/
