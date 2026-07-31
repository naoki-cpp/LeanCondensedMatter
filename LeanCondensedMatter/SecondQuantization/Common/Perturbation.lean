import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansionVerification
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries

set_option linter.style.header false

/-!
# Finite-basis perturbative infrastructure

Coefficientwise interval integration, statistics-independent Dyson coefficients, and their finite
trace power series for algebraic endomorphisms on a finite configuration basis. These constructions
remain algebraic; convergence and normed continuous-operator realizations are handled separately.
-/
