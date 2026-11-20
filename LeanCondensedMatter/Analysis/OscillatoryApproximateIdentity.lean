import LeanCondensedMatter.Analysis.OscillatoryIntegral
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-! # A conditional approximate-identity bridge for the finite-time oscillatory kernel

The unit-time energy profile is the squared norm of the actual phase integral,
with the standard 2π normalization. Its decay at infinity is derived from
the nonresonant sine formula; Mathlib's general peak-function theorem then
supplies its scaled limit provided the sinc-square unit-mass integral is established.
-/

namespace OscillatoryIntegral
noncomputable section
open Filter MeasureTheory Bornology
open scoped Topology

/-- The nonnegative unit-time spectral profile. -/
def spectralProfile (frequency : ℝ) : ℝ :=
  ‖timeIntegral frequency 1‖ ^ 2 / (2 * Real.pi)

theorem spectralProfile_nonneg (frequency : ℝ) :
    0 ≤ spectralProfile frequency := by
  unfold spectralProfile
  positivity

/-- The unit-time spectral profile decays fast enough for the peak-function theorem.
The estimate uses the nonresonant sine formula; no Fourier transform is needed. -/
theorem spectralProfile_decay :
    Tendsto (fun frequency : ℝ => ‖frequency‖ * spectralProfile frequency)
      (cobounded ℝ) (𝓝 0) := by
  have hbound (x : ℝ) :
      ‖x‖ * spectralProfile x ≤ (2 / Real.pi) * ‖x⁻¹‖ := by
    by_cases hx : x = 0
    · subst x
      simp
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hsq : x ^ 2 = ‖x‖ ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      rw [spectralProfile, norm_timeIntegral_sq x 1 hx]
      simp only [mul_one]
      rw [hsq]
      calc
        ‖x‖ * ((4 * Real.sin (x / 2) ^ 2 / ‖x‖ ^ 2) / (2 * Real.pi)) =
            (2 / Real.pi) * (Real.sin (x / 2) ^ 2 / ‖x‖) := by
              field_simp [ne_of_gt hn, Real.pi_ne_zero]
              ring
        _ ≤ (2 / Real.pi) * (1 / ‖x‖) := by
          gcongr
          exact Real.sin_sq_le_one (x / 2)
        _ = (2 / Real.pi) * ‖x⁻¹‖ := by
          rw [norm_inv]
          ring
  have hinv : Tendsto (fun x : ℝ => ‖x⁻¹‖) (cobounded ℝ) (𝓝 0) := by
    simpa using (Filter.tendsto_inv₀_cobounded (α := ℝ)).norm
  exact squeeze_zero
    (fun x => mul_nonneg (norm_nonneg x) (spectralProfile_nonneg x))
    hbound (by simpa using hinv.const_mul (2 / Real.pi))

/-- A normalized, sufficiently decaying finite-time spectral profile converges
against an integrable test density continuous at the resonant energy.
The remaining sinc-square unit-mass identity is an explicit hypothesis;
the pointwise decay needed for concentration is proved above. -/
theorem tendsto_scaled_spectralProfile_of_mass
    (hMass : ∫ frequency : ℝ, spectralProfile frequency = 1)
    (density : ℝ → ℝ) (hDensity : Integrable density)
    (hContinuous : ContinuousAt density 0) :
    Tendsto
      (fun time : ℝ => ∫ energy : ℝ,
        (time * spectralProfile (time * energy)) * density energy)
      atTop (𝓝 (density 0)) := by
  have h := tendsto_integral_comp_smul_smul_of_integrable
    (φ := spectralProfile) spectralProfile_nonneg hMass
    (by simpa using spectralProfile_decay) hDensity hContinuous
  simpa only [Module.finrank_self, pow_one, smul_eq_mul] using h

end
end OscillatoryIntegral
