import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteAnalyticBridge
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDyson
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansionVerification
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries

set_option linter.style.header false

/-!
# Finite-basis perturbative infrastructure

Coefficientwise interval integration, its finite-dimensional continuous-operator realization,
statistics-independent algebraic and continuous Dyson coefficients, and their finite trace power
series for endomorphisms on a finite configuration basis.
-/
