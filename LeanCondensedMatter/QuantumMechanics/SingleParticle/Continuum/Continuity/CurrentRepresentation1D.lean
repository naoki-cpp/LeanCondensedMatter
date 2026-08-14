import LeanCondensedMatter.Analysis.Calculus.CurrentRepresentation
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.Schwartz1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Local current representations for one-dimensional Schwartz wavefunctions

This module connects the representation-independent weak-current API to a concrete one-dimensional
continuum realization.  Real Schwartz test functions are differentiated by the canonical Schwartz
derivative, and a real Schwartz current density `j` is paired with a test 1-form `α` by

`∫ x, α x * j x`.

Because differentiation, multiplication, and integration are all bundled linear maps on Schwartz
space, this gives an actual `ConservationLaw.LocalCurrentDensityRepresentation` rather than a
pointwise formula carrying separate integrability hypotheses.

The second part bundles the usual Schrödinger probability current of a complex Schwartz
wavefunction as a real Schwartz current density and proves the whole-space weak continuity identity
for arbitrary real Schwartz test functions.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory

/-- Real part of a complex Schwartz wavefunction, still a real Schwartz function. -/
def schwartzRealPart1D (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  ψ.postcompCLM Complex.reCLM

/-- Imaginary part of a complex Schwartz wavefunction, still a real Schwartz function. -/
def schwartzImaginaryPart1D (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  ψ.postcompCLM Complex.imCLM

@[simp]
theorem schwartzRealPart1D_apply (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzRealPart1D ψ x = (ψ x).re :=
  rfl

@[simp]
theorem schwartzImaginaryPart1D_apply (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzImaginaryPart1D ψ x = (ψ x).im :=
  rfl

/-- The real Schwartz function representing `Im (star ψ * χ)`. -/
noncomputable def schwartzProbabilityCurrentPairing1D
    (ψ χ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ)
      (schwartzRealPart1D ψ) (schwartzImaginaryPart1D χ) -
    SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ)
      (schwartzImaginaryPart1D ψ) (schwartzRealPart1D χ)

@[simp]
theorem schwartzProbabilityCurrentPairing1D_apply
    (ψ χ : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzProbabilityCurrentPairing1D ψ χ x =
      probabilityCurrentPairingValue (ψ x) (χ x) := by
  change (ψ x).re * (χ x).im - (ψ x).im * (χ x).re =
    probabilityCurrentPairingValue (ψ x) (χ x)
  exact (probabilityCurrentPairingValue_eq_coordinates (ψ x) (χ x)).symm

/-- The standard one-dimensional probability current, bundled as a real Schwartz function. -/
noncomputable def schwartzProbabilityCurrent1D
    (ℏ κ : ℝ) (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  (2 * κ / ℏ) •
    schwartzProbabilityCurrentPairing1D ψ (schwartzSpatialDerivative1D ψ)

@[simp]
theorem schwartzProbabilityCurrent1D_apply
    (ℏ κ : ℝ) (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzProbabilityCurrent1D ℏ κ ψ x =
      probabilityCurrentValue1D ℏ κ (ψ x) (schwartzSpatialDerivative1D ψ x) := by
  change (2 * κ / ℏ) *
      schwartzProbabilityCurrentPairing1D ψ (schwartzSpatialDerivative1D ψ) x = _
  rw [schwartzProbabilityCurrentPairing1D_apply]
  rfl

/-- The canonical derivative on real one-dimensional Schwartz test functions, regarded as a linear
map for the abstract current-representation API. -/
noncomputable def schwartzDifferential1D :
    SchwartzMap ℝ ℝ →ₗ[ℝ] SchwartzMap ℝ ℝ :=
  (SchwartzMap.derivCLM ℝ ℝ).toLinearMap

@[simp]
theorem schwartzDifferential1D_apply (test : SchwartzMap ℝ ℝ) (x : ℝ) :
    schwartzDifferential1D test x = deriv test x :=
  rfl

/-- Zeroth-order local pairing `j, α ↦ ∫ α(x) j(x) dx` for real Schwartz current densities. -/
noncomputable def schwartzLocalCurrentPairing1D :
    ConservationLaw.LocalCurrentPairing
      (𝕜 := ℝ)
      (OneForm := SchwartzMap ℝ ℝ)
      (Obs := ℝ)
      (CurrentDensity := SchwartzMap ℝ ℝ) where
  toFun := fun current =>
    ((SchwartzMap.integralCLM ℝ volume).comp
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ).flip current)).toLinearMap
  map_add' := by
    intro j₁ j₂
    ext α
    simp
  map_smul' := by
    intro c j
    ext α
    simp

@[simp]
theorem schwartzLocalCurrentPairing1D_apply
    (current α : SchwartzMap ℝ ℝ) :
    schwartzLocalCurrentPairing1D current α = ∫ x, α x * current x :=
  rfl

/-- Weak transport functional represented by one real Schwartz current density. -/
noncomputable def schwartzWeakTransportFunctional1D
    (current : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ →ₗ[ℝ] ℝ :=
  (schwartzLocalCurrentPairing1D current).comp schwartzDifferential1D

@[simp]
theorem schwartzWeakTransportFunctional1D_apply
    (current test : SchwartzMap ℝ ℝ) :
    schwartzWeakTransportFunctional1D current test =
      ∫ x, deriv test x * current x :=
  rfl

/-- Every real Schwartz current density gives a local current-density representation of its weak
transport functional. -/
noncomputable def schwartzLocalCurrentDensityRepresentation1D
    (current : SchwartzMap ℝ ℝ) :
    ConservationLaw.LocalCurrentDensityRepresentation
      schwartzDifferential1D
      (schwartzWeakTransportFunctional1D current)
      schwartzLocalCurrentPairing1D where
  currentDensity := current
  represents := by
    intro test
    rfl

/-- The usual Schrödinger probability current is one concrete local current-density
representation. -/
noncomputable def schwartzProbabilityCurrentRepresentation1D
    (ℏ κ : ℝ) (ψ : SchwartzMap ℝ ℂ) :
    ConservationLaw.LocalCurrentDensityRepresentation
      schwartzDifferential1D
      (schwartzWeakTransportFunctional1D (schwartzProbabilityCurrent1D ℏ κ ψ))
      schwartzLocalCurrentPairing1D :=
  schwartzLocalCurrentDensityRepresentation1D (schwartzProbabilityCurrent1D ℏ κ ψ)

/-- Spatial differentiation of the bundled Schwartz probability current gives the standard
probability-current divergence. -/
theorem deriv_schwartzProbabilityCurrent1D
    (ℏ κ : ℝ) (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (schwartzProbabilityCurrent1D ℏ κ ψ) x =
      probabilityCurrentDivergenceValue1D ℏ κ (ψ x)
        (schwartzSpatialSecondDerivative1D ψ x) := by
  have hcurrent := hasDerivAt_probabilityCurrentValue1D ℏ κ
    (hasDerivAt_schwartzSpatialDerivative1D_re ψ x)
    (hasDerivAt_schwartzSpatialDerivative1D_im ψ x)
    (hasDerivAt_schwartzSpatialSecondDerivative1D_re ψ x)
    (hasDerivAt_schwartzSpatialSecondDerivative1D_im ψ x)
  calc
    deriv (schwartzProbabilityCurrent1D ℏ κ ψ) x =
        deriv (fun y => probabilityCurrentValue1D ℏ κ (ψ y)
          (schwartzSpatialDerivative1D ψ y)) x := by
      apply congrArg (fun f : ℝ → ℝ => deriv f x)
      funext y
      exact schwartzProbabilityCurrent1D_apply ℏ κ ψ y
    _ = probabilityCurrentDivergenceValue1D ℏ κ (ψ x)
        (schwartzSpatialSecondDerivative1D ψ x) := hcurrent.deriv

/-- Whole-space weak Schrödinger continuity for an arbitrary real Schwartz test function.

The right-hand side is exactly the transport functional represented by the bundled local
probability-current density.  No separate spatial integrability or boundary assumptions are needed
because both the test and current are Schwartz functions. -/
theorem schrodinger_weak_continuity_wholeSpace_of_schwartz
    (ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    (test : SchwartzMap ℝ ℝ) (ψ : SchwartzMap ℝ ℂ)
    {ψt : ℝ → ℂ} {potential : ℝ → ℝ}
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt x =
        -(κ : ℂ) * schwartzSpatialSecondDerivative1D ψ x +
          (potential x : ℂ) * ψ x) :
    (∫ x, test x * probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      schwartzWeakTransportFunctional1D (schwartzProbabilityCurrent1D ℏ κ ψ) test := by
  let current := schwartzProbabilityCurrent1D ℏ κ ψ
  have hpointwise : ∀ x,
      probabilityDensityTimeDerivativeValue (ψ x) (ψt x) = -deriv current x := by
    intro x
    have hbalance := probability_continuity_balance_of_schrodinger
      ℏ κ (potential x) (ψ x) (ψt x)
        (schwartzSpatialSecondDerivative1D ψ x) hℏ (hschrodinger x)
    have hcurrent : deriv current x =
        probabilityCurrentDivergenceValue1D ℏ κ (ψ x)
          (schwartzSpatialSecondDerivative1D ψ x) := by
      simpa [current] using deriv_schwartzProbabilityCurrent1D ℏ κ ψ x
    rw [← hcurrent] at hbalance
    linarith
  calc
    (∫ x, test x * probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
        ∫ x, -(test x * deriv current x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hpointwise x]
      ring
    _ = -(∫ x, test x * deriv current x) := by
      rw [integral_neg]
    _ = ∫ x, deriv test x * current x := by
      rw [SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul test current]
      simp
    _ = schwartzWeakTransportFunctional1D current test := by
      exact (schwartzWeakTransportFunctional1D_apply current test).symm
    _ = schwartzWeakTransportFunctional1D (schwartzProbabilityCurrent1D ℏ κ ψ) test := by
      rfl

end
end Continuum
end SingleParticle
end QuantumMechanics
