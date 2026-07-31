import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansionVerification

set_option linter.style.header false

/-!
# Finite-basis perturbative infrastructure

Coefficientwise interval integration and statistics-independent Dyson coefficients for algebraic
endomorphisms on a finite configuration basis. These constructions remain algebraic; convergence
and normed continuous-operator realizations are handled separately.
-/
