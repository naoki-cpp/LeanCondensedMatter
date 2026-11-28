import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.Weak1D
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Schrödinger continuity for Schwartz spatial wavefunctions

This module specializes the one-dimensional continuum continuity kernel to spatial Schwartz
wavefunctions. The first and second spatial derivatives remain in Schwartz space, which
supplies the spatial differentiability hypotheses of the pointwise and interval-weak continuity
theorems.

Time differentiability and the pointwise Schrödinger equation remain explicit. This keeps the
continuity argument independent of any self-adjoint unbounded-Hamiltonian construction on `L²`.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped Interval

/-- The first spatial derivative of a complex Schwartz wavefunction, still in Schwartz space. -/
def schwartzSpatialDerivative1D (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.derivCLM ℂ ℂ ψ

/-- The second spatial derivative of a complex Schwartz wavefunction, still in Schwartz space. -/
def schwartzSpatialSecondDerivative1D (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.derivCLM ℂ ℂ (schwartzSpatialDerivative1D ψ)

@[simp]
theorem schwartzSpatialDerivative1D_apply (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzSpatialDerivative1D ψ x = deriv ψ x :=
  rfl

@[simp]
theorem schwartzSpatialSecondDerivative1D_apply (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzSpatialSecondDerivative1D ψ x = deriv (schwartzSpatialDerivative1D ψ) x :=
  rfl

/-- A Schwartz wavefunction has the canonical first derivative at every spatial point. -/
theorem hasDerivAt_schwartzSpatialDerivative1D (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ψ y) (schwartzSpatialDerivative1D ψ x) x := by
  simpa [schwartzSpatialDerivative1D] using (SchwartzMap.hasDerivAt ψ x)

/-- The first Schwartz derivative has the canonical second derivative at every spatial point. -/
theorem hasDerivAt_schwartzSpatialSecondDerivative1D (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => schwartzSpatialDerivative1D ψ y)
      (schwartzSpatialSecondDerivative1D ψ x) x := by
  change HasDerivAt (schwartzSpatialDerivative1D ψ)
    (deriv (schwartzSpatialDerivative1D ψ) x) x
  exact SchwartzMap.hasDerivAt (schwartzSpatialDerivative1D ψ) x

/-- Pointwise Schrödinger continuity with all spatial differentiability supplied by a Schwartz
wavefunction. Only the time-slice differentiability and pointwise equation of motion remain
explicit. -/
theorem oneDimensional_schrodinger_continuity_of_schwartz
    (ℏ κ potential : ℝ) (hℏ : ℏ ≠ 0)
    {ψTime : ℝ → ℂ} (ψSpace : SchwartzMap ℝ ℂ) {ψt : ℂ} {t x : ℝ}
    (hsame : ψTime t = ψSpace x)
    (htime : HasDerivAt ψTime ψt t)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        -(κ : ℂ) * schwartzSpatialSecondDerivative1D ψSpace x +
          (potential : ℂ) * ψSpace x) :
    deriv (fun s => probabilityDensityValue (ψTime s)) t +
      deriv (fun y => probabilityCurrentValue1D ℏ κ (ψSpace y)
        (schwartzSpatialDerivative1D ψSpace y)) x = 0 := by
  exact oneDimensional_schrodinger_continuity ℏ κ potential hℏ hsame
    htime
    (hasDerivAt_schwartzSpatialDerivative1D ψSpace x)
    (hasDerivAt_schwartzSpatialSecondDerivative1D ψSpace x)
    hschrodinger

/-- Interval weak Schrödinger continuity with all spatial differentiability supplied by a Schwartz
wavefunction. The current-divergence integrability hypothesis remains explicit. -/
theorem schrodinger_weak_continuity_interval_of_schwartz
    (a b ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    {test testDerivative : ℝ → ℝ}
    (ψ : SchwartzMap ℝ ℂ) {ψt : ℝ → ℂ} {potential : ℝ → ℝ}
    (htest : ∀ x ∈ Set.uIcc a b, HasDerivAt test (testDerivative x) x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt x =
        -(κ : ℂ) * schwartzSpatialSecondDerivative1D ψ x +
          (potential x : ℂ) * ψ x)
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => probabilityCurrentDivergenceValue1D ℏ κ (ψ x)
        (schwartzSpatialSecondDerivative1D ψ x)) volume a b) :
    (∫ x in a..b, test x * probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      (∫ x in a..b, testDerivative x * probabilityCurrentValue1D ℏ κ (ψ x)
            (schwartzSpatialDerivative1D ψ x)) -
        weightedBoundaryCurrent1D a b test
          (fun x => probabilityCurrentValue1D ℏ κ (ψ x)
            (schwartzSpatialDerivative1D ψ x)) := by
  apply schrodinger_weak_continuity_interval a b ℏ κ hℏ htest
  · intro x _
    exact hasDerivAt_schwartzSpatialDerivative1D ψ x
  · intro x _
    exact hasDerivAt_schwartzSpatialSecondDerivative1D ψ x
  · exact hschrodinger
  · exact htestIntegrable
  · exact hcurrentIntegrable

end
end Continuum
end SingleParticle
end QuantumMechanics
