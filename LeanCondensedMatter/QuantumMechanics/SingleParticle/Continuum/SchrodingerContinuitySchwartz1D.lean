import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.Weak1D
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Schrödinger continuity for Schwartz spatial wavefunctions

This module specializes the one-dimensional continuum continuity kernel to spatial Schwartz
wavefunctions. The first and second spatial derivatives remain in Schwartz space, so the pointwise
and interval-weak continuity theorems no longer need coordinatewise spatial differentiability
hypotheses supplied by callers.

Time differentiability and the pointwise Schrödinger equation remain explicit. This keeps the
continuity argument independent of any self-adjoint unbounded-Hamiltonian construction on `L²`.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory

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

private theorem hasDerivAt_realPart_of_complex
    {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).re) f'.re x := by
  have hderiv := (Complex.reCLM.hasFDerivAt.comp x h.hasFDerivAt).hasDerivAt
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at hderiv
  simpa using hderiv

private theorem hasDerivAt_imaginaryPart_of_complex
    {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).im) f'.im x := by
  have hderiv := (Complex.imCLM.hasFDerivAt.comp x h.hasFDerivAt).hasDerivAt
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at hderiv
  simpa using hderiv

/-- Real-coordinate derivative data for a Schwartz wavefunction is automatic. -/
theorem hasDerivAt_schwartzSpatialDerivative1D_re (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (fun y => (ψ y).re) (schwartzSpatialDerivative1D ψ x).re x :=
  hasDerivAt_realPart_of_complex (hasDerivAt_schwartzSpatialDerivative1D ψ x)

/-- Imaginary-coordinate derivative data for a Schwartz wavefunction is automatic. -/
theorem hasDerivAt_schwartzSpatialDerivative1D_im (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (fun y => (ψ y).im) (schwartzSpatialDerivative1D ψ x).im x :=
  hasDerivAt_imaginaryPart_of_complex (hasDerivAt_schwartzSpatialDerivative1D ψ x)

/-- Real-coordinate second derivative data for a Schwartz wavefunction is automatic. -/
theorem hasDerivAt_schwartzSpatialSecondDerivative1D_re (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (fun y => (schwartzSpatialDerivative1D ψ y).re)
      (schwartzSpatialSecondDerivative1D ψ x).re x :=
  hasDerivAt_realPart_of_complex (hasDerivAt_schwartzSpatialSecondDerivative1D ψ x)

/-- Imaginary-coordinate second derivative data for a Schwartz wavefunction is automatic. -/
theorem hasDerivAt_schwartzSpatialSecondDerivative1D_im (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (fun y => (schwartzSpatialDerivative1D ψ y).im)
      (schwartzSpatialSecondDerivative1D ψ x).im x :=
  hasDerivAt_imaginaryPart_of_complex (hasDerivAt_schwartzSpatialSecondDerivative1D ψ x)

/-- Pointwise Schrödinger continuity with all spatial differentiability supplied by a Schwartz
wavefunction. Only the time-slice differentiability and pointwise equation of motion remain
explicit. -/
theorem oneDimensional_schrodinger_continuity_of_schwartz
    (ℏ κ potential : ℝ) (hℏ : ℏ ≠ 0)
    {ψTime : ℝ → ℂ} (ψSpace : SchwartzMap ℝ ℂ) {ψt : ℂ} {t x : ℝ}
    (hsame : ψTime t = ψSpace x)
    (htimeRe : HasDerivAt (fun s => (ψTime s).re) ψt.re t)
    (htimeIm : HasDerivAt (fun s => (ψTime s).im) ψt.im t)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        -(κ : ℂ) * schwartzSpatialSecondDerivative1D ψSpace x +
          (potential : ℂ) * ψSpace x) :
    deriv (fun s => probabilityDensityValue (ψTime s)) t +
      deriv (fun y => probabilityCurrentValue1D ℏ κ (ψSpace y)
        (schwartzSpatialDerivative1D ψSpace y)) x = 0 := by
  exact oneDimensional_schrodinger_continuity ℏ κ potential hℏ hsame
    htimeRe htimeIm
    (hasDerivAt_schwartzSpatialDerivative1D_re ψSpace x)
    (hasDerivAt_schwartzSpatialDerivative1D_im ψSpace x)
    (hasDerivAt_schwartzSpatialSecondDerivative1D_re ψSpace x)
    (hasDerivAt_schwartzSpatialSecondDerivative1D_im ψSpace x)
    hschrodinger

/-- Interval weak Schrödinger continuity with all spatial differentiability supplied by a Schwartz
wavefunction. The remaining current-divergence integrability hypothesis is kept explicit for this
first Schwartz slice. -/
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
    intervalSmearedDensityRate1D a b test
        (fun x => probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      intervalSmearedCurrentPairing1D a b testDerivative
          (fun x => probabilityCurrentValue1D ℏ κ (ψ x)
            (schwartzSpatialDerivative1D ψ x)) -
        weightedBoundaryCurrent1D a b test
          (fun x => probabilityCurrentValue1D ℏ κ (ψ x)
            (schwartzSpatialDerivative1D ψ x)) := by
  apply schrodinger_weak_continuity_interval a b ℏ κ hℏ htest
  · intro x _
    exact hasDerivAt_schwartzSpatialDerivative1D_re ψ x
  · intro x _
    exact hasDerivAt_schwartzSpatialDerivative1D_im ψ x
  · intro x _
    exact hasDerivAt_schwartzSpatialSecondDerivative1D_re ψ x
  · intro x _
    exact hasDerivAt_schwartzSpatialSecondDerivative1D_im ψ x
  · exact hschrodinger
  · exact htestIntegrable
  · exact hcurrentIntegrable

end
end Continuum
end SingleParticle
end QuantumMechanics
