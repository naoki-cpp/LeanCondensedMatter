import LeanCondensedMatter.Analysis.OscillatoryIntegral
import Mathlib.MeasureTheory.Integral.PeakFunction

set_option linter.style.header false

/-! # A conditional approximate-identity bridge for the finite-time oscillatory kernel

The unit-time energy profile is the squared norm of the actual phase integral,
with the standard 2π normalization. Mathlib's general peak-function theorem
then supplies its scaled limit, provided its unit mass and decay are established.

These two hypotheses are deliberately explicit: the unit-mass identity is a
nontrivial sinc-square integral and is not implied by pointwise normalization.
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

/-- A normalized, sufficiently decaying finite-time spectral profile converges
against an integrable test density continuous at the resonant energy.
The remaining sinc-square unit-mass and decay identities are stated as explicit
hypotheses rather than being hidden in the definition. -/
theorem tendsto_scaled_spectralProfile_of_mass_and_decay
    (hMass : ∫ frequency : ℝ, spectralProfile frequency = 1)
    (hDecay : Tendsto (fun frequency : ℝ => ‖frequency‖ * spectralProfile frequency)
      (cobounded ℝ) (𝓝 0))
    (density : ℝ → ℝ) (hDensity : Integrable density)
    (hContinuous : ContinuousAt density 0) :
    Tendsto
      (fun time : ℝ => ∫ energy : ℝ,
        (time * spectralProfile (time * energy)) * density energy)
      atTop (𝓝 (density 0)) := by
  have h := tendsto_integral_comp_smul_smul_of_integrable
    (φ := spectralProfile) spectralProfile_nonneg hMass
    (by simpa using hDecay) hDensity hContinuous
  simpa only [Module.finrank_self, pow_one, smul_eq_mul] using h

end
end OscillatoryIntegral
