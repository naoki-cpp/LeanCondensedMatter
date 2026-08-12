import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerContinuitySchwartz1D
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Whole-space probability balance for Schwartz wavefunctions in one dimension

This module uses rapid decay of Schwartz wavefunctions to remove the spatial boundary term from the
one-dimensional Schrödinger continuity equation. The first result is the whole-space rate identity

`∫ ∂ₜρ = 0`.

It deliberately stops one step before differentiating the total probability integral with respect to
time. That final step only needs a separate differentiation-under-the-integral hypothesis and does
not require any unbounded-operator or self-adjointness theory.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory

/-- Real part of a complex Schwartz wavefunction, still a Schwartz function. -/
private def schwartzRealPart1D (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  ψ.postcompCLM Complex.reCLM

/-- Imaginary part of a complex Schwartz wavefunction, still a Schwartz function. -/
private def schwartzImaginaryPart1D (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  ψ.postcompCLM Complex.imCLM

@[simp]
private theorem schwartzRealPart1D_apply (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzRealPart1D ψ x = (ψ x).re :=
  rfl

@[simp]
private theorem schwartzImaginaryPart1D_apply (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzImaginaryPart1D ψ x = (ψ x).im :=
  rfl

@[simp]
private theorem deriv_schwartzRealPart1D (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (schwartzRealPart1D ψ) x = (schwartzSpatialDerivative1D ψ x).re := by
  have h : HasDerivAt (schwartzRealPart1D ψ)
      (schwartzSpatialDerivative1D ψ x).re x := by
    change HasDerivAt (fun y : ℝ => (ψ y).re)
      (schwartzSpatialDerivative1D ψ x).re x
    exact hasDerivAt_schwartzSpatialDerivative1D_re ψ x
  exact h.deriv

@[simp]
private theorem deriv_schwartzImaginaryPart1D (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (schwartzImaginaryPart1D ψ) x = (schwartzSpatialDerivative1D ψ x).im := by
  have h : HasDerivAt (schwartzImaginaryPart1D ψ)
      (schwartzSpatialDerivative1D ψ x).im x := by
    change HasDerivAt (fun y : ℝ => (ψ y).im)
      (schwartzSpatialDerivative1D ψ x).im x
    exact hasDerivAt_schwartzSpatialDerivative1D_im ψ x
  exact h.deriv

private theorem integrable_mul_schwartz1D (f g : SchwartzMap ℝ ℝ) :
    Integrable (fun x : ℝ => f x * g x) (volume : Measure ℝ) := by
  change Integrable
    (fun x : ℝ => (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f g) x)
    (volume : Measure ℝ)
  exact (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f g).integrable

/-- The integral of the probability-current divergence vanishes for a Schwartz wavefunction.

This is the whole-space boundary cancellation. It follows directly from Schwartz integration by
parts applied to the real and imaginary components of the wavefunction. -/
theorem integral_probabilityCurrentDivergenceValue1D_of_schwartz_eq_zero
    (ℏ κ : ℝ) (ψ : SchwartzMap ℝ ℂ) :
    (∫ x, probabilityCurrentDivergenceValue1D ℏ κ (ψ x)
      (schwartzSpatialSecondDerivative1D ψ x)) = 0 := by
  have hReIm :
      (∫ x, (ψ x).re * (schwartzSpatialSecondDerivative1D ψ x).im) =
        -∫ x, (schwartzSpatialDerivative1D ψ x).re *
          (schwartzSpatialDerivative1D ψ x).im := by
    simpa [schwartzSpatialSecondDerivative1D] using
      (SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul
        (schwartzRealPart1D ψ)
        (schwartzImaginaryPart1D (schwartzSpatialDerivative1D ψ)))
  have hImRe :
      (∫ x, (ψ x).im * (schwartzSpatialSecondDerivative1D ψ x).re) =
        -∫ x, (schwartzSpatialDerivative1D ψ x).im *
          (schwartzSpatialDerivative1D ψ x).re := by
    simpa [schwartzSpatialSecondDerivative1D] using
      (SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul
        (schwartzImaginaryPart1D ψ)
        (schwartzRealPart1D (schwartzSpatialDerivative1D ψ)))
  have hMixed :
      (∫ x, (schwartzSpatialDerivative1D ψ x).re *
        (schwartzSpatialDerivative1D ψ x).im) =
      ∫ x, (schwartzSpatialDerivative1D ψ x).im *
        (schwartzSpatialDerivative1D ψ x).re := by
    apply integral_congr_ae
    filter_upwards with x
    exact mul_comm _ _
  have hCross :
      (∫ x, (ψ x).re * (schwartzSpatialSecondDerivative1D ψ x).im) =
        ∫ x, (ψ x).im * (schwartzSpatialSecondDerivative1D ψ x).re := by
    calc
      (∫ x, (ψ x).re * (schwartzSpatialSecondDerivative1D ψ x).im) =
          -∫ x, (schwartzSpatialDerivative1D ψ x).re *
            (schwartzSpatialDerivative1D ψ x).im := hReIm
      _ = -∫ x, (schwartzSpatialDerivative1D ψ x).im *
            (schwartzSpatialDerivative1D ψ x).re := by rw [hMixed]
      _ = ∫ x, (ψ x).im * (schwartzSpatialSecondDerivative1D ψ x).re := hImRe.symm
  have hLeft : Integrable
      (fun x => (ψ x).re * (schwartzSpatialSecondDerivative1D ψ x).im) := by
    simpa using integrable_mul_schwartz1D
      (schwartzRealPart1D ψ)
      (schwartzImaginaryPart1D (schwartzSpatialSecondDerivative1D ψ))
  have hRight : Integrable
      (fun x => (ψ x).im * (schwartzSpatialSecondDerivative1D ψ x).re) := by
    simpa using integrable_mul_schwartz1D
      (schwartzImaginaryPart1D ψ)
      (schwartzRealPart1D (schwartzSpatialSecondDerivative1D ψ))
  calc
    (∫ x, probabilityCurrentDivergenceValue1D ℏ κ (ψ x)
        (schwartzSpatialSecondDerivative1D ψ x)) =
      ∫ x, (2 * κ / ℏ) •
        ((ψ x).re * (schwartzSpatialSecondDerivative1D ψ x).im -
          (ψ x).im * (schwartzSpatialSecondDerivative1D ψ x).re) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [probabilityCurrentDivergenceValue1D_eq_coordinates]
        simp [smul_eq_mul]
    _ = (2 * κ / ℏ) •
        (∫ x, (ψ x).re * (schwartzSpatialSecondDerivative1D ψ x).im -
          (ψ x).im * (schwartzSpatialSecondDerivative1D ψ x).re) := by
        rw [integral_smul]
    _ = (2 * κ / ℏ) •
        ((∫ x, (ψ x).re * (schwartzSpatialSecondDerivative1D ψ x).im) -
          ∫ x, (ψ x).im * (schwartzSpatialSecondDerivative1D ψ x).re) := by
        rw [integral_sub hLeft hRight]
    _ = 0 := by rw [hCross, sub_self, smul_zero]

/-- A scalar-potential Schrödinger equation has zero whole-space probability-density rate for a
Schwartz spatial wavefunction. -/
theorem integral_probabilityDensityTimeDerivativeValue_of_schrodinger_schwartz_eq_zero
    (ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    (ψ : SchwartzMap ℝ ℂ) {ψt : ℝ → ℂ} {potential : ℝ → ℝ}
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt x =
        -(κ : ℂ) * schwartzSpatialSecondDerivative1D ψ x +
          (potential x : ℂ) * ψ x) :
    (∫ x, probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) = 0 := by
  have hpointwise : ∀ x,
      probabilityDensityTimeDerivativeValue (ψ x) (ψt x) =
        -probabilityCurrentDivergenceValue1D ℏ κ (ψ x)
          (schwartzSpatialSecondDerivative1D ψ x) := by
    intro x
    have hbalance := probability_continuity_balance_of_schrodinger
      ℏ κ (potential x) (ψ x) (ψt x)
        (schwartzSpatialSecondDerivative1D ψ x) hℏ (hschrodinger x)
    linarith
  calc
    (∫ x, probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
        ∫ x, -probabilityCurrentDivergenceValue1D ℏ κ (ψ x)
          (schwartzSpatialSecondDerivative1D ψ x) := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpointwise x
    _ = -(∫ x, probabilityCurrentDivergenceValue1D ℏ κ (ψ x)
          (schwartzSpatialSecondDerivative1D ψ x)) := by rw [integral_neg]
    _ = 0 := by
      rw [integral_probabilityCurrentDivergenceValue1D_of_schwartz_eq_zero]
      simp

end
end Continuum
end SingleParticle
end QuantumMechanics
