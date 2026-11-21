import LeanCondensedMatter.Transport.Analysis.PolarFourierRadialDerivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr

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

/-- The reciprocal quadratic resolvent norm is bounded by the
inverse half-dispersion beyond the center-dependent UV threshold. -/
theorem massiveDiracRadialCenter_inv_norm_le_half_quadratic_inv
    (v p : ℝ) (center : ℂ) (hv : v ≠ 0)
    (hp : max (1 : ℝ)
        (2 * ‖center‖ / v ^ 2) ≤ p) :
    ‖(center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹‖ ≤
      (v ^ 2 * p ^ 2 / 2)⁻¹ := by
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
        center =
        -(((v ^ 2 * p ^ 2 : ℝ) : ℂ)) := by
    ring
  have htri :=
    norm_sub_le (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)) center
  rw [hdiff, norm_neg, hnorm] at htri
  have hden : v ^ 2 * p ^ 2 / 2 ≤
      ‖center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)‖ := by
    linarith
  have hpos : 0 < v ^ 2 * p ^ 2 / 2 := by positivity
  have hnormpos : 0 < ‖center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)‖ :=
    lt_of_lt_of_le hpos hden
  rw [norm_inv, inv_le_inv₀ hnormpos hpos]
  exact hden

/-- The ultraviolet boundary term in the radial Fourier integration-by-parts
identity vanishes for a quadratic spectral-center denominator with nonzero
velocity. The proof uses only the explicit quadratic resolvent bound and
the uniform `2π` bound on the first angular harmonic, not Bessel asymptotics. -/
theorem massiveDiracRadialCenter_firstHarmonicBoundary_tendsto_zero
    (v c : ℝ) (center : ℂ) (hv : v ≠ 0) :
    Filter.Tendsto
      (fun p : ℝ => (p : ℂ) *
        polarFourierFirstCosineAngularKernel (p * c) *
          ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹)
      Filter.atTop (nhds 0) := by
  let cutoff : ℝ := max 1 (2 * ‖center‖ / v ^ 2)
  let coeff : ℝ := 4 * Real.pi / v ^ 2
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hpoint (p : ℝ) (hp : cutoff ≤ p) :
      ‖(p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹‖ ≤
        coeff / p := by
    have hp1 : 1 ≤ p := (le_max_left _ _).trans hp
    have hp0 : 0 < p := by linarith
    have hK := polarFourierFirstCosineAngularKernel_norm_le (p * c)
    have hD := massiveDiracRadialCenter_inv_norm_le_half_quadratic_inv
      v p (center) hv hp
    calc
      ‖(p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹‖ =
          p * ‖polarFourierFirstCosineAngularKernel (p * c)‖ *
            ‖((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
      _ ≤ p * (2 * Real.pi) *
            ‖((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹‖ := by
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
          ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹‖)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun p => norm_nonneg _
    · filter_upwards [Filter.eventually_ge_atTop cutoff] with p hp
      exact hpoint p hp
    · exact hlimit
  exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm


end

end QuantumTheory.Models.MassiveDirac

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
theorem massiveDiracRadialFourierRemainder_norm_le_center
    (v c p : ℝ) (center : ℂ) (hv : v ≠ 0)
    (hp : max (1 : ℝ)
        (2 * ‖center‖ / v ^ 2) ≤ p) :
    ‖(p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
        ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
          ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2)‖ ≤
      (16 * Real.pi / v ^ 2) * p ^ (-2 : ℝ) := by
  have hp1 : 1 ≤ p := (le_max_left _ _).trans hp
  have hp0 : 0 < p := by linarith
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hK := polarFourierFirstCosineAngularKernel_norm_le (p * c)
  have hD := massiveDiracRadialCenter_inv_norm_le_half_quadratic_inv
    v p (center) hv hp
  have hnorm :
      ‖(p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
            ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2)‖ =
      (p * ‖polarFourierFirstCosineAngularKernel (p * c)‖) *
        (2 * v ^ 2 * p) *
        ‖((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹‖ ^ 2 := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp0, Complex.norm_two]
    rw [sq_abs]
    ring
  rw [hnorm]
  calc
    (p * ‖polarFourierFirstCosineAngularKernel (p * c)‖) *
        (2 * v ^ 2 * p) *
        ‖((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹‖ ^ 2 ≤
      (p * (2 * Real.pi)) * (2 * v ^ 2 * p) *
        ((v ^ 2 * p ^ 2 / 2)⁻¹) ^ 2 := by
      gcongr
    _ = (16 * Real.pi / v ^ 2) * p ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_two]
      field_simp [ne_of_gt hp0, pow_ne_zero 2 hv]
      ring

/-- Integrability on any ultraviolet half-line beyond the explicit
quadratic-dominance threshold. The complex spectral center is held fixed. -/
theorem massiveDiracRadialFourierRemainder_integrableOn_uv_center
    (v c a : ℝ) (center : ℂ) (hv : v ≠ 0)
    (hden : ∀ p : ℝ, (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)) ≠ 0)
    (ha : max (1 : ℝ)
        (2 * ‖center‖ / v ^ 2) ≤ a) :
    IntegrableOn
      (fun p : ℝ =>
        (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
            ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2))
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
      (fun p : ℝ => (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))) := by
    fun_prop
  have hInvCont : Continuous
      (fun p : ℝ => ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹) :=
    hDcont.inv₀ hden
  have hKcont : Continuous
      (fun p : ℝ => polarFourierFirstCosineAngularKernel (p * c)) :=
    continuous_polarFourierFirstCosineAngularKernel.comp
      (continuous_id.mul continuous_const)
  have hf : Continuous (fun p : ℝ =>
      (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
        ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
          ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2)) :=
    ((Complex.continuous_ofReal.comp continuous_id).mul hKcont).mul
      ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_id)).mul
        (hInvCont.pow 2))
  apply hmajor.mono' hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact massiveDiracRadialFourierRemainder_norm_le_center v c p center hv
    (ha.trans hp.le)



end

end QuantumTheory.Models.MassiveDirac
