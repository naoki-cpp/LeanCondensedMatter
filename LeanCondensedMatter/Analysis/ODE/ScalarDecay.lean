import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Scalar linear decay equation

The integrating factor reduces the constant-coefficient real differential
equation to a function with vanishing derivative.
-/

namespace Real

/-- A globally differentiable real function satisfying the scalar decay equation
is determined by its initial value. The coefficient need not be positive. -/
theorem eq_initial_mul_exp_neg_of_hasDerivAt (rate : ℝ) (f : ℝ → ℝ)
    (hderiv : ∀ t, HasDerivAt f (-(rate * f t)) t) (t : ℝ) :
    f t = f 0 * Real.exp (-(rate * t)) := by
  let g : ℝ → ℝ := fun s => f s * Real.exp (rate * s)
  have hgzero (s : ℝ) : HasDerivAt g 0 s := by
    have he : HasDerivAt (fun u : ℝ => Real.exp (rate * u))
        (Real.exp (rate * s) * rate) s := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id s).const_mul rate).exp)
    change HasDerivAt (fun u : ℝ => f u * Real.exp (rate * u)) 0 s
    convert (hderiv s).mul he using 1
    ring
  have h := is_const_of_deriv_eq_zero
    (fun s => (hgzero s).differentiableAt)
    (fun s => (hgzero s).deriv) t 0
  simpa [g, mul_assoc, ← Real.exp_add] using
    congrArg (fun x : ℝ => x * Real.exp (-(rate * t))) h

end Real
