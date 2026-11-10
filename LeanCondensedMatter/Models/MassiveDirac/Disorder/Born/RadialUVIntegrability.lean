import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVBound
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.style.header false

/-!
# Integrability of the massive-Dirac radial Fourier remainder

At a fixed complex energy and mass with nonvanishing quadratic
denominator, integration by parts produces a residual integrand with
two inverse denominators. The radial polynomial prefactor and the
bounded first angular harmonic leave an integrable `p⁻²` majorant
on the ultraviolet half-line.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory

/-- The differentiated massive-Dirac resolvent remainder is at most
`16π/(v²p²)` beyond the explicit quadratic-dominance threshold. -/
theorem massiveDiracRadialFourierRemainder_norm_le
    (v c p : ℝ) (energy mass : ℂ) (hv : v ≠ 0)
    (hp : max (1 : ℝ)
        (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2) ≤ p) :
    ‖(p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
        ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2)‖ ≤
      (16 * Real.pi / v ^ 2) * p ^ (-2 : ℝ) := by
  have hp1 : 1 ≤ p := (le_max_left _ _).trans hp
  have hp0 : 0 < p := by linarith
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hK := polarFourierFirstCosineAngularKernel_norm_le (p * c)
  have hD := massiveDiracRadialCenter_inv_norm_le_half_quadratic_inv
    v p (energy ^ 2 - mass ^ 2) hv hp
  change ‖(massiveDiracRadialDenominator v p energy mass)⁻¹‖ ≤ _ at hD
  have hnorm :
      ‖(p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2)‖ =
      (p * ‖polarFourierFirstCosineAngularKernel (p * c)‖) *
        (2 * v ^ 2 * p) *
        ‖(massiveDiracRadialDenominator v p energy mass)⁻¹‖ ^ 2 := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp0, Complex.norm_two]
    rw [sq_abs]
    ring
  rw [hnorm]
  calc
    (p * ‖polarFourierFirstCosineAngularKernel (p * c)‖) *
        (2 * v ^ 2 * p) *
        ‖(massiveDiracRadialDenominator v p energy mass)⁻¹‖ ^ 2 ≤
      (p * (2 * Real.pi)) * (2 * v ^ 2 * p) *
        ((v ^ 2 * p ^ 2 / 2)⁻¹) ^ 2 := by
      gcongr
    _ = (16 * Real.pi / v ^ 2) * p ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_two]
      field_simp [ne_of_gt hp0, pow_ne_zero 2 hv]
      ring

/-- Integrability on any ultraviolet half-line beyond the explicit
quadratic-dominance threshold. The complex spectral center is held fixed. -/
theorem massiveDiracRadialFourierRemainder_integrableOn_uv
    (v c a : ℝ) (energy mass : ℂ) (hv : v ≠ 0)
    (hden : ∀ p : ℝ, massiveDiracRadialDenominator v p energy mass ≠ 0)
    (ha : max (1 : ℝ)
        (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2) ≤ a) :
    IntegrableOn
      (fun p : ℝ =>
        (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2))
      (Set.Ioi a) := by
  have ha1 : 1 ≤ a := (le_max_left _ _).trans ha
  have ha0 : 0 < a := by linarith
  have hpow : IntegrableOn (fun p : ℝ => p ^ (-2 : ℝ)) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha0
  have hmajor :
      IntegrableOn (fun p : ℝ =>
        (16 * Real.pi / v ^ 2) * p ^ (-2 : ℝ)) (Set.Ioi a) :=
    hpow.const_mul _
  have hDcont : Continuous
      (fun p : ℝ => massiveDiracRadialDenominator v p energy mass) := by
    unfold massiveDiracRadialDenominator
    fun_prop
  have hInvCont : Continuous
      (fun p : ℝ => (massiveDiracRadialDenominator v p energy mass)⁻¹) :=
    hDcont.inv₀ hden
  have hKcont : Continuous
      (fun p : ℝ => polarFourierFirstCosineAngularKernel (p * c)) :=
    continuous_polarFourierFirstCosineAngularKernel.comp
      (continuous_id.mul continuous_const)
  have hf : Continuous (fun p : ℝ =>
      (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
        ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2)) :=
    ((Complex.continuous_ofReal.comp continuous_id).mul hKcont).mul
      ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_id)).mul
        (hInvCont.pow 2))
  apply hmajor.mono' hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact massiveDiracRadialFourierRemainder_norm_le v c p energy mass hv
    (ha.trans hp.le)

end

end QuantumTheory.Models.MassiveDirac
