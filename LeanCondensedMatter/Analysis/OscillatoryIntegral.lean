import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-! # Finite-time oscillatory integral

The integral of exp(iωs) on [0,t], including resonance and its squared norm.
No Hamiltonian, Planck constant, density of states, or long-time limit is used.
-/
namespace OscillatoryIntegral
noncomputable section
open MeasureTheory

/-- The finite-time phase integral, defined also at zero frequency. -/
def timeIntegral (frequency time : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..time, Complex.exp (Complex.I * ((frequency * s : ℝ) : ℂ))

/-- Exact nonresonant phase integral. -/
theorem timeIntegral_of_ne_zero (frequency time : ℝ) (hfrequency : frequency ≠ 0) :
    timeIntegral frequency time =
      (Complex.exp (Complex.I * ((frequency * time : ℝ) : ℂ)) - 1) /
        (Complex.I * (frequency : ℂ)) := by
  have hc : Complex.I * (frequency : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hfrequency)
  simpa only [timeIntegral, Complex.ofReal_mul, mul_assoc, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero] using
    (integral_exp_mul_complex (a := 0) (b := time) hc)

/-- The resonant phase integral is the elapsed time. -/
theorem timeIntegral_zero (time : ℝ) : timeIntegral 0 time = (time : ℂ) := by
  simp [timeIntegral]

/-- The nonresonant squared integral is the familiar finite-time sine kernel. -/
theorem norm_timeIntegral_sq (frequency time : ℝ) (hfrequency : frequency ≠ 0) :
    ‖timeIntegral frequency time‖ ^ 2 =
      4 * Real.sin (frequency * time / 2) ^ 2 / frequency ^ 2 := by
  rw [timeIntegral_of_ne_zero frequency time hfrequency]
  simp only [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, div_pow, mul_pow, sq_abs]
  ring

end
end OscillatoryIntegral
