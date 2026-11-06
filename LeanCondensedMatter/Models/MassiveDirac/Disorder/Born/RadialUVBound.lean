import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialKernel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Ultraviolet lower bounds for the massive-Dirac radial denominator

At momenta larger than the explicit scale fixed by the complex spectral
center, the quadratic dispersion dominates the center in norm. The bounds
are uniform in the angular variable and independent of the Born
approximation, supplying the elementary large-momentum resolvent estimate
required by the real-space Gaussian-crossed sector.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

/-- The massive-Dirac radial denominator is bounded below by half its
quadratic momentum term beyond an explicit positive threshold. This is
a norm estimate for an arbitrary complex energy and mass, not an
asymptotic statement that assumes a real spectral pole. -/
theorem massiveDiracRadialDenominator_norm_ge_half_quadratic
    (v p : ℝ) (energy mass : ℂ) (hv : v ≠ 0)
    (hp : max (1 : ℝ)
        (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2) ≤ p) :
    v ^ 2 * p ^ 2 / 2 ≤
      ‖massiveDiracRadialDenominator v p energy mass‖ := by
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hp1 : 1 ≤ p := (le_max_left _ _).trans hp
  have hpA : 2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2 ≤ p :=
    (le_max_right _ _).trans hp
  have hAp : 2 * ‖energy ^ 2 - mass ^ 2‖ ≤ v ^ 2 * p := by
    have h := (div_le_iff₀ hv2).mp hpA
    nlinarith
  have hp2 : p ≤ p ^ 2 := by nlinarith
  have hAp2 : 2 * ‖energy ^ 2 - mass ^ 2‖ ≤ v ^ 2 * p ^ 2 := by
    have hmul := mul_nonneg hv2.le (sub_nonneg.mpr hp2)
    nlinarith
  have hquad : 0 ≤ v ^ 2 * p ^ 2 := mul_nonneg (sq_nonneg v) (sq_nonneg p)
  have hnorm :
      ‖(((v ^ 2 * p ^ 2 : ℝ) : ℂ))‖ = v ^ 2 * p ^ 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hquad]
  have hdiff :
      massiveDiracRadialDenominator v p energy mass -
        (energy ^ 2 - mass ^ 2) =
        -(((v ^ 2 * p ^ 2 : ℝ) : ℂ)) := by
    unfold massiveDiracRadialDenominator
    push_cast
    ring
  have htri :=
    norm_sub_le (massiveDiracRadialDenominator v p energy mass)
      (energy ^ 2 - mass ^ 2)
  rw [hdiff, norm_neg, hnorm] at htri
  linarith

/-- The corresponding inverse quadratic-denominator norm is bounded by
the reciprocal half-dispersion. Both the positive threshold and
nonvanishing of the denominator follow from the bound itself. -/
theorem massiveDiracRadialDenominator_inv_norm_le_half_quadratic_inv
    (v p : ℝ) (energy mass : ℂ) (hv : v ≠ 0)
    (hp : max (1 : ℝ)
        (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2) ≤ p) :
    ‖(massiveDiracRadialDenominator v p energy mass)⁻¹‖ ≤
      (v ^ 2 * p ^ 2 / 2)⁻¹ := by
  have hden := massiveDiracRadialDenominator_norm_ge_half_quadratic
    v p energy mass hv hp
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hp1 : 1 ≤ p := (le_max_left _ _).trans hp
  have hpos : 0 < v ^ 2 * p ^ 2 / 2 := by positivity
  have hnorm : 0 < ‖massiveDiracRadialDenominator v p energy mass‖ :=
    lt_of_lt_of_le hpos hden
  rw [norm_inv, inv_le_inv₀ hnorm hpos]
  exact hden

end

end QuantumTheory.Models.MassiveDirac
