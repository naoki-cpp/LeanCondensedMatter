import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Regularized hypergeometric coefficients and the J₀ Bessel series

Model-independent formulas for integer-shifted lower parameters of
regularized hypergeometric functions and the complete complex J₀ Taylor
series. The Fourier-angular applications are separate consumers.
-/

namespace BesselHypergeometric

/-- The coefficient of the regularized hypergeometric series with lower parameter `k + 1`. -/
theorem regularizedHGFunCoeff_zero_singleton_nat_add_one (k n : ℕ) :
    Complex.regularizedHGFunCoeff 0 {((k + 1 : ℕ) : ℂ)} n =
      1 / ((Nat.factorial n : ℂ) * (Nat.factorial (n + k) : ℂ)) := by
  have hgamma : Complex.Gamma (((k : ℂ) + 1) + (n : ℂ)) =
      (Nat.factorial (n + k) : ℂ) := by
    rw [show ((k : ℂ) + 1) + (n : ℂ) = ((n + k : ℕ) : ℂ) + 1 by
      simp only [Nat.cast_add]
      ring]
    exact Complex.Gamma_nat_eq_factorial (n + k)
  simp [Complex.regularizedHGFunCoeff, Nat.cast_add, hgamma]

/-- Mathlib's integer-order Bessel function has the expected coefficient expansion. -/
theorem besselJZero_eq_regularizedHGTsum (z : ℂ) :
    Complex.besselJ 0 z =
      ∑' n : ℕ, Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} n *
        (-(z / 2) ^ 2) ^ n := by
  rw [Complex.besselJ_def]
  simp only [Complex.cpow_zero, one_mul, zero_add]
  change (Complex.regularizedHGFunSeries 0 {(1 : ℂ)}).sum (-(z / 2) ^ 2) = _
  rw [Complex.regularizedHGFunSeries, ← FormalMultilinearSeries.ofScalarsSum,
    FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]

end BesselHypergeometric
