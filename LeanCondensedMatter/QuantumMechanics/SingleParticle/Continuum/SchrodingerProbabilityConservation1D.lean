import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.SchwartzIntegral1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Probability.Integral1D
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Total probability conservation for Schwartz Schrödinger wavefunctions in one dimension

This module performs the final analytic step from the whole-space density-rate identity to an actual
time derivative of the total probability. Differentiation under the spatial integral is justified by
explicit dominated-derivative hypotheses. For a Schwartz spatial slice satisfying the scalar-potential
Schrödinger equation, the resulting derivative is zero.

No closed-operator, self-adjointness, or unitary-evolution construction is used.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory Set

/-- Differentiate the total probability under the whole-space integral.

The hypotheses are the global analogue of the dominated-derivative assumptions used for the
interval-smeared continuity theorem. -/
theorem hasDerivAt_totalProbability1D
    (t : ℝ)
    {s : Set ℝ} {bound : ℝ → ℝ}
    {ψ ψt : ℝ → ℝ → ℂ}
    (hs : s ∈ nhds t)
    (hDensityMeas : ∀ τ ∈ s,
      AEStronglyMeasurable (fun x => probabilityDensityValue (ψ τ x)) volume)
    (hDensityIntegrable : Integrable
      (fun x => probabilityDensityValue (ψ t x)) volume)
    (hDensityRateMeas : AEStronglyMeasurable
      (fun x => probabilityDensityTimeDerivativeValue (ψ t x) (ψt t x)) volume)
    (hBound : ∀ x, ∀ τ ∈ s,
      ‖probabilityDensityTimeDerivativeValue (ψ τ x) (ψt τ x)‖ ≤ bound x)
    (hBoundIntegrable : Integrable bound volume)
    (htimeRe : ∀ x, ∀ τ ∈ s,
      HasDerivAt (fun u => (ψ u x).re) (ψt τ x).re τ)
    (htimeIm : ∀ x, ∀ τ ∈ s,
      HasDerivAt (fun u => (ψ u x).im) (ψt τ x).im τ) :
    HasDerivAt
      (fun τ => totalProbability1D (ψ τ))
      (∫ x, probabilityDensityTimeDerivativeValue (ψ t x) (ψt t x)) t := by
  have hFMeas : ∀ᶠ τ in nhds t,
      AEStronglyMeasurable (fun x => probabilityDensityValue (ψ τ x)) volume := by
    filter_upwards [hs] with τ hτ
    exact hDensityMeas τ hτ
  have hBoundAE : ∀ᵐ x ∂volume, ∀ τ ∈ s,
      ‖probabilityDensityTimeDerivativeValue (ψ τ x) (ψt τ x)‖ ≤ bound x :=
    Filter.Eventually.of_forall fun x τ hτ => hBound x τ hτ
  have hDiff : ∀ᵐ x ∂volume, ∀ τ ∈ s,
      HasDerivAt
        (fun u => probabilityDensityValue (ψ u x))
        (probabilityDensityTimeDerivativeValue (ψ τ x) (ψt τ x)) τ :=
    Filter.Eventually.of_forall fun x τ hτ =>
      hasDerivAt_probabilityDensityValue (htimeRe x τ hτ) (htimeIm x τ hτ)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ x => probabilityDensityValue (ψ τ x))
    (F' := fun τ x => probabilityDensityTimeDerivativeValue (ψ τ x) (ψt τ x))
    hs hFMeas hDensityIntegrable hDensityRateMeas hBoundAE hBoundIntegrable hDiff
  simpa [totalProbability1D] using h.2

/-- A Schwartz-valued scalar-potential Schrödinger trajectory conserves total probability at `t`
under the explicit dominated time-differentiation hypotheses. -/
theorem hasDerivAt_totalProbability1D_of_schrodinger_schwartz
    (t ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    {s : Set ℝ} {bound : ℝ → ℝ}
    (ψ : ℝ → SchwartzMap ℝ ℂ) {ψt : ℝ → ℝ → ℂ} {potential : ℝ → ℝ}
    (hs : s ∈ nhds t)
    (hDensityMeas : ∀ τ ∈ s,
      AEStronglyMeasurable (fun x => probabilityDensityValue (ψ τ x)) volume)
    (hDensityIntegrable : Integrable
      (fun x => probabilityDensityValue (ψ t x)) volume)
    (hDensityRateMeas : AEStronglyMeasurable
      (fun x => probabilityDensityTimeDerivativeValue (ψ t x) (ψt t x)) volume)
    (hBound : ∀ x, ∀ τ ∈ s,
      ‖probabilityDensityTimeDerivativeValue (ψ τ x) (ψt τ x)‖ ≤ bound x)
    (hBoundIntegrable : Integrable bound volume)
    (htimeRe : ∀ x, ∀ τ ∈ s,
      HasDerivAt (fun u => (ψ u x).re) (ψt τ x).re τ)
    (htimeIm : ∀ x, ∀ τ ∈ s,
      HasDerivAt (fun u => (ψ u x).im) (ψt τ x).im τ)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt t x =
        -(κ : ℂ) * schwartzSpatialSecondDerivative1D (ψ t) x +
          (potential x : ℂ) * ψ t x) :
    HasDerivAt (fun τ => totalProbability1D (ψ τ)) 0 t := by
  have hdensity := hasDerivAt_totalProbability1D
    (ψ := fun τ x => ψ τ x) (ψt := ψt) t hs hDensityMeas hDensityIntegrable
      hDensityRateMeas hBound hBoundIntegrable htimeRe htimeIm
  have hzero :=
    integral_probabilityDensityTimeDerivativeValue_of_schrodinger_schwartz_eq_zero
      ℏ κ hℏ (ψ t) (ψt := ψt t) hschrodinger
  rw [hzero] at hdensity
  exact hdensity

/-- Pointwise derivative form of Schwartz total-probability conservation. -/
theorem deriv_totalProbability1D_of_schrodinger_schwartz_eq_zero
    (t ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    {s : Set ℝ} {bound : ℝ → ℝ}
    (ψ : ℝ → SchwartzMap ℝ ℂ) {ψt : ℝ → ℝ → ℂ} {potential : ℝ → ℝ}
    (hs : s ∈ nhds t)
    (hDensityMeas : ∀ τ ∈ s,
      AEStronglyMeasurable (fun x => probabilityDensityValue (ψ τ x)) volume)
    (hDensityIntegrable : Integrable
      (fun x => probabilityDensityValue (ψ t x)) volume)
    (hDensityRateMeas : AEStronglyMeasurable
      (fun x => probabilityDensityTimeDerivativeValue (ψ t x) (ψt t x)) volume)
    (hBound : ∀ x, ∀ τ ∈ s,
      ‖probabilityDensityTimeDerivativeValue (ψ τ x) (ψt τ x)‖ ≤ bound x)
    (hBoundIntegrable : Integrable bound volume)
    (htimeRe : ∀ x, ∀ τ ∈ s,
      HasDerivAt (fun u => (ψ u x).re) (ψt τ x).re τ)
    (htimeIm : ∀ x, ∀ τ ∈ s,
      HasDerivAt (fun u => (ψ u x).im) (ψt τ x).im τ)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt t x =
        -(κ : ℂ) * schwartzSpatialSecondDerivative1D (ψ t) x +
          (potential x : ℂ) * ψ t x) :
    deriv (fun τ => totalProbability1D (ψ τ)) t = 0 :=
  (hasDerivAt_totalProbability1D_of_schrodinger_schwartz
    t ℏ κ hℏ ψ hs hDensityMeas hDensityIntegrable hDensityRateMeas hBound
      hBoundIntegrable htimeRe htimeIm hschrodinger).deriv

end
end Continuum
end SingleParticle
end QuantumMechanics
