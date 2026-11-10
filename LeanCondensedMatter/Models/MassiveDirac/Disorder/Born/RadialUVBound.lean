import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialKernel
import LeanCondensedMatter.Transport.Analysis.PolarFourierRadialDerivative
import Mathlib.Tactic.FieldSimp
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

open QuantumTheory.Transport

/-- The massive-Dirac radial denominator is bounded below by half its
quadratic momentum term beyond an explicit positive threshold. This is
a norm estimate for an arbitrary complex spectral center, not an
asymptotic statement that assumes a real spectral pole. -/
theorem massiveDiracRadialCenter_norm_ge_half_quadratic
    (v p : ℝ) (center : ℂ) (hv : v ≠ 0)
    (hp : max (1 : ℝ)
        (2 * ‖center‖ / v ^ 2) ≤ p) :
    v ^ 2 * p ^ 2 / 2 ≤
      ‖(center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))‖ := by
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hp1 : 1 ≤ p := (le_max_left _ _).trans hp
  have hpA : 2 * ‖center‖ / v ^ 2 ≤ p :=
    (le_max_right _ _).trans hp
  have hAp : 2 * ‖center‖ ≤ v ^ 2 * p := by
    have h := (div_le_iff₀ hv2).mp hpA
    nlinarith
  have hp2 : p ≤ p ^ 2 := by nlinarith
  have hAp2 : 2 * ‖center‖ ≤ v ^ 2 * p ^ 2 := by
    have hmul := mul_nonneg hv2.le (sub_nonneg.mpr hp2)
    nlinarith
  have hquad : 0 ≤ v ^ 2 * p ^ 2 := mul_nonneg (sq_nonneg v) (sq_nonneg p)
  have hnorm :
      ‖(((v ^ 2 * p ^ 2 : ℝ) : ℂ))‖ = v ^ 2 * p ^ 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hquad]
  have hdiff :
      (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)) -
        (center) =
        -(((v ^ 2 * p ^ 2 : ℝ) : ℂ)) := by
    ring
  have htri :=
    norm_sub_le ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))
      (center)
  rw [hdiff, norm_neg, hnorm] at htri
  linarith

/-- The corresponding inverse quadratic-denominator norm is bounded by
the reciprocal half-dispersion. Both the positive threshold and
nonvanishing of the denominator follow from the bound itself. -/
theorem massiveDiracRadialCenter_inv_norm_le_half_quadratic_inv
    (v p : ℝ) (center : ℂ) (hv : v ≠ 0)
    (hp : max (1 : ℝ)
        (2 * ‖center‖ / v ^ 2) ≤ p) :
    ‖((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹‖ ≤
      (v ^ 2 * p ^ 2 / 2)⁻¹ := by
  have hden := massiveDiracRadialCenter_norm_ge_half_quadratic
    v p energy mass hv hp
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hp1 : 1 ≤ p := (le_max_left _ _).trans hp
  have hpos : 0 < v ^ 2 * p ^ 2 / 2 := by positivity
  have hnorm : 0 < ‖(center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))‖ :=
    lt_of_lt_of_le hpos hden
  rw [norm_inv, inv_le_inv₀ hnorm hpos]
  exact hden

/-- The ultraviolet boundary term in the radial Fourier integration-by-parts
identity vanishes for a quadratic massive-Dirac denominator with nonzero
velocity. The proof uses only the explicit quadratic resolvent bound and
the uniform `2π` bound on the first angular harmonic, not Bessel asymptotics. -/
theorem massiveDiracRadialDenominator_firstHarmonicBoundary_tendsto_zero
    (v c : ℝ) (energy mass : ℂ) (hv : v ≠ 0) :
    Filter.Tendsto
      (fun p : ℝ => (p : ℂ) *
        polarFourierFirstCosineAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹)
      Filter.atTop (nhds 0) := by
  let cutoff : ℝ := max 1 (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2)
  let coeff : ℝ := 4 * Real.pi / v ^ 2
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hpoint (p : ℝ) (hp : cutoff ≤ p) :
      ‖(p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹‖ ≤
        coeff / p := by
    have hp1 : 1 ≤ p := (le_max_left _ _).trans hp
    have hp0 : 0 < p := by linarith
    have hK := polarFourierFirstCosineAngularKernel_norm_le (p * c)
    have hD :
        ‖(massiveDiracRadialDenominator v p energy mass)⁻¹‖ ≤
          (v ^ 2 * p ^ 2 / 2)⁻¹ := by
      simpa only [massiveDiracRadialDenominator] using
        (massiveDiracRadialCenter_inv_norm_le_half_quadratic_inv
          v p (energy ^ 2 - mass ^ 2) hv hp)
    calc
      ‖(p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹‖ =
          p * ‖polarFourierFirstCosineAngularKernel (p * c)‖ *
            ‖(massiveDiracRadialDenominator v p energy mass)⁻¹‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
      _ ≤ p * (2 * Real.pi) *
            ‖(massiveDiracRadialDenominator v p energy mass)⁻¹‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left hK hp0.le
      _ ≤ p * (2 * Real.pi) * (v ^ 2 * p ^ 2 / 2)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hD
          (mul_nonneg hp0.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le))
      _ = coeff / p := by
        dsimp [coeff]
        field_simp [ne_of_gt hp0, pow_ne_zero 2 hv]
        ring
  have hlimit : Filter.Tendsto (fun p : ℝ => coeff / p)
      Filter.atTop (nhds 0) := by
    simpa only [id_eq] using
      (Filter.tendsto_id : Filter.Tendsto (fun p : ℝ => p)
        Filter.atTop Filter.atTop).const_div_atTop coeff
  have hnorm : Filter.Tendsto
      (fun p : ℝ => ‖(p : ℂ) *
        polarFourierFirstCosineAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹‖)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun p => norm_nonneg _
    · filter_upwards [Filter.eventually_ge_atTop cutoff] with p hp
      exact hpoint p hp
    · exact hlimit
  exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm

end

end QuantumTheory.Models.MassiveDirac
