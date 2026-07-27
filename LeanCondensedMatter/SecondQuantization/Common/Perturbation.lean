import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral

set_option linter.style.header false

/-!
# Finite-basis perturbative infrastructure

Coefficientwise interval integration of endomorphism-valued functions on a finite occupation basis.
This is kept separate because the present reconstruction of an operator from all matrix coefficients
requires a finite configuration type; a convergence-aware bosonic analogue is not yet available.
-/
