import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Regularized hypergeometric coefficients at positive integer parameters

With no upper parameters and one positive integer lower parameter, the coefficient is
the reciprocal of a product of factorials.
-/

namespace Complex

/-- The coefficient of the regularized hypergeometric series with lower parameter `k + 1`. -/
theorem regularizedHGFunCoeff_zero_singleton_nat_add_one (k n : ℕ) :
    regularizedHGFunCoeff 0 {((k + 1 : ℕ) : ℂ)} n =
      1 / ((Nat.factorial n : ℂ) * (Nat.factorial (n + k) : ℂ)) := by
  have hgamma : Gamma (((k : ℂ) + 1) + (n : ℂ)) =
      (Nat.factorial (n + k) : ℂ) := by
    rw [show ((k : ℂ) + 1) + (n : ℂ) = ((n + k : ℕ) : ℂ) + 1 by
      simp only [Nat.cast_add]
      ring]
    exact Gamma_nat_eq_factorial (n + k)
  simp [regularizedHGFunCoeff, Nat.cast_add, hgamma]

end Complex
