import LeanCondensedMatter.SecondQuantization.Common.Algebra.Statistics
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false

/-!
# Scalar exchange denominator

The fermionic exchange sign makes the scalar denominator in the
Bloch--de Dominicis two-point argument strictly positive at every
real inverse temperature and real energy shift. This is a fact about
statistics and scalar exponentials, not about a chosen Gibbs ensemble
or the validity of a state-specific KMS or pairing recurrence.
-/

namespace SecondQuantization.Common.BlochDeDominicis

/-- The fermionic exchange denominator never vanishes for real shifts and temperatures. -/
theorem one_sub_zetaInt_fermion_mul_exp_ne_zero (x β : ℝ) :
    (1 : ℂ) - ((Statistics.fermion.zetaInt : ℤ) : ℂ) *
        Complex.exp ((x * β : ℝ) : ℂ) ≠ 0 := by
  have hpos : (0 : ℝ) < 1 + Real.exp (x * β) := by
    positivity
  have heq : (1 : ℂ) - ((Statistics.fermion.zetaInt : ℤ) : ℂ) *
      Complex.exp ((x * β : ℝ) : ℂ) = ((1 + Real.exp (x * β) : ℝ) : ℂ) := by
    rw [Statistics.zetaInt_fermion]
    push_cast [Complex.ofReal_exp]
    ring
  rw [heq]
  exact_mod_cast hpos.ne'

end SecondQuantization.Common.BlochDeDominicis
