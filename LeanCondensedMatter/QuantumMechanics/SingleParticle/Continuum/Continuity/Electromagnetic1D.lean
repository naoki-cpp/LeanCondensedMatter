import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Electromagnetic.Current1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.Scalar1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Electromagnetic.MinimalCoupling1D
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Gauge-covariant Schrödinger continuity equation in one dimension

This module derives the pointwise electromagnetic probability and charge continuity equations from
the minimal-coupling algebra in `Electromagnetic/MinimalCoupling1D` and the current in
`Electromagnetic/Current1D`.

The vector potential and its spatial derivative are explicit theorem inputs. No magnetic operator on
`L²` or self-adjointness statement is introduced here.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

/-- The value obtained by differentiating the electromagnetic probability current in space. The
second term is the product-rule derivative of `A |ψ|²`. -/
def electromagneticProbabilityCurrentDivergenceValue1D
    (q ℏ mass vectorPotential vectorPotentialDerivative : ℝ)
    (ψ ψx ψxx : ℂ) : ℝ :=
  (ℏ / mass) * (ψ.re * ψxx.im - ψ.im * ψxx.re) -
    (q / mass) *
      (vectorPotentialDerivative * probabilityDensityValue ψ +
        vectorPotential * probabilityDensityTimeDerivativeValue ψ ψx)

/-- Differentiating the gauge-covariant current uses the product rule for the vector potential and
for the wavefunction. -/
theorem hasDerivAt_electromagneticProbabilityCurrentValue1D
    (q ℏ mass : ℝ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    {vectorPotential : ℝ → ℝ} {vectorPotentialDerivative : ℝ}
    {ψ ψx : ℝ → ℂ} {ψxx : ℂ} {x : ℝ}
    (hA : HasDerivAt vectorPotential vectorPotentialDerivative x)
    (hψ : HasDerivAt ψ (ψx x) x)
    (hψx : HasDerivAt ψx ψxx x) :
    HasDerivAt
      (fun y => electromagneticProbabilityCurrentValue1D
        q ℏ mass (vectorPotential y) (ψ y) (ψx y))
      (electromagneticProbabilityCurrentDivergenceValue1D
        q ℏ mass (vectorPotential x) vectorPotentialDerivative (ψ x) (ψx x) ψxx) x := by
  have hcoeff : ℏ / mass = 2 * (ℏ ^ 2 / (2 * mass)) / ℏ := by
    field_simp [hℏ, hmass]
  have hparamagnetic :
      HasDerivAt
        (fun y => (ℏ / mass) * ((ψ y).re * (ψx y).im - (ψ y).im * (ψx y).re))
        ((ℏ / mass) * ((ψ x).re * ψxx.im - (ψ x).im * ψxx.re)) x := by
    rw [hcoeff]
    simpa only [probabilityCurrentValue1D_eq_coordinates,
      probabilityCurrentDivergenceValue1D_eq_coordinates] using
      (hasDerivAt_probabilityCurrentValue1D ℏ (ℏ ^ 2 / (2 * mass)) hψ hψx)
  have hdensity := hasDerivAt_probabilityDensityValue hψ
  have hdiamagnetic := (HasDerivAt.mul hA hdensity).const_mul (q / mass)
  have hraw := HasDerivAt.sub hparamagnetic hdiamagnetic
  have hfun :
      (fun y => electromagneticProbabilityCurrentValue1D
        q ℏ mass (vectorPotential y) (ψ y) (ψx y)) =
      (fun y =>
        (ℏ / mass) * ((ψ y).re * (ψx y).im - (ψ y).im * (ψx y).re) -
          (q / mass) * (vectorPotential y * probabilityDensityValue (ψ y))) := by
    funext y
    rw [electromagneticProbabilityCurrentValue1D_eq_expanded
      q ℏ mass (vectorPotential y) (ψ y) (ψx y) hℏ hmass]
    ring
  rw [hfun]
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at hraw
  simpa [electromagneticProbabilityCurrentDivergenceValue1D,
    Pi.mul_apply, Pi.sub_apply, Pi.add_apply] using hraw

/-- Pointwise probability balance derived directly from the minimally coupled Schrödinger equation.
The real scalar-potential contribution cancels, while the `A` and `Aₓ` terms assemble into the
covariant current divergence. -/
theorem electromagnetic_probability_continuity_balance_of_schrodinger
    (q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential : ℝ)
    (ψ ψt ψx ψxx : ℂ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential ψ ψx ψxx) :
    probabilityDensityTimeDerivativeValue ψ ψt +
      electromagneticProbabilityCurrentDivergenceValue1D
        q ℏ mass vectorPotential vectorPotentialDerivative ψ ψx ψxx = 0 := by
  rw [minimallyCoupledSchrodingerRhsValue1D_eq_expanded
    q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential ψ ψx ψxx hmass]
    at hschrodinger
  have him := congrArg (fun z : ℂ => (star ψ * z).im) hschrodinger
  simp at him
  simp only [electromagneticProbabilityCurrentDivergenceValue1D,
    probabilityDensityTimeDerivativeValue, probabilityDensityValue, Complex.normSq_apply]
  linear_combination (norm := skip) (2 / ℏ) * him
  field_simp [hℏ, hmass]
  ring

/-- One-dimensional pointwise electromagnetic Schrödinger continuity equation. All time, space,
and vector-potential derivatives used in the proof are explicit hypotheses. -/
theorem oneDimensional_electromagnetic_schrodinger_continuity
    (q ℏ mass scalarPotential : ℝ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    {ψTime ψSpace ψx : ℝ → ℂ} {vectorPotential : ℝ → ℝ}
    {ψt ψxx : ℂ} {vectorPotentialDerivative : ℝ} {t x : ℝ}
    (hsame : ψTime t = ψSpace x)
    (htime : HasDerivAt ψTime ψt t)
    (hspace : HasDerivAt ψSpace (ψx x) x)
    (hspaceDerivative : HasDerivAt ψx ψxx x)
    (hvectorPotential : HasDerivAt vectorPotential vectorPotentialDerivative x)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass (vectorPotential x) vectorPotentialDerivative scalarPotential
          (ψSpace x) (ψx x) ψxx) :
    deriv (fun s => probabilityDensityValue (ψTime s)) t +
      deriv (fun y => electromagneticProbabilityCurrentValue1D
        q ℏ mass (vectorPotential y) (ψSpace y) (ψx y)) x = 0 := by
  rw [(hasDerivAt_probabilityDensityValue htime).deriv,
    (hasDerivAt_electromagneticProbabilityCurrentValue1D
      q ℏ mass hℏ hmass hvectorPotential hspace
      hspaceDerivative).deriv]
  rw [hsame]
  exact electromagnetic_probability_continuity_balance_of_schrodinger
    q ℏ mass (vectorPotential x) vectorPotentialDerivative scalarPotential
    (ψSpace x) ψt (ψx x) ψxx hℏ hmass hschrodinger

/-- Charge continuity follows from probability continuity by the same `j_q = q j` scaling as in the
scalar-potential theory. -/
theorem oneDimensional_electromagnetic_charge_continuity
    (q ℏ mass scalarPotential : ℝ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    {ψTime ψSpace ψx : ℝ → ℂ} {vectorPotential : ℝ → ℝ}
    {ψt ψxx : ℂ} {vectorPotentialDerivative : ℝ} {t x : ℝ}
    (hsame : ψTime t = ψSpace x)
    (htime : HasDerivAt ψTime ψt t)
    (hspace : HasDerivAt ψSpace (ψx x) x)
    (hspaceDerivative : HasDerivAt ψx ψxx x)
    (hvectorPotential : HasDerivAt vectorPotential vectorPotentialDerivative x)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass (vectorPotential x) vectorPotentialDerivative scalarPotential
          (ψSpace x) (ψx x) ψxx) :
    deriv (fun s => chargeDensityValue q (ψTime s)) t +
      deriv (fun y => electromagneticChargeCurrentValue1D
        q ℏ mass (vectorPotential y) (ψSpace y) (ψx y)) x = 0 := by
  have hdensity := hasDerivAt_probabilityDensityValue htime
  have hcurrent := hasDerivAt_electromagneticProbabilityCurrentValue1D
    q ℏ mass hℏ hmass hvectorPotential hspace
    hspaceDerivative
  have hchargeDensity :
      HasDerivAt (fun s => chargeDensityValue q (ψTime s))
        (q * probabilityDensityTimeDerivativeValue (ψTime t) ψt) t := by
    simpa [chargeDensityValue] using hdensity.const_mul q
  have hchargeCurrent :
      HasDerivAt
        (fun y => electromagneticChargeCurrentValue1D
          q ℏ mass (vectorPotential y) (ψSpace y) (ψx y))
        (q * electromagneticProbabilityCurrentDivergenceValue1D
          q ℏ mass (vectorPotential x) vectorPotentialDerivative
          (ψSpace x) (ψx x) ψxx) x := by
    simpa [electromagneticChargeCurrentValue1D] using hcurrent.const_mul q
  rw [hchargeDensity.deriv, hchargeCurrent.deriv, hsame, ← mul_add]
  rw [electromagnetic_probability_continuity_balance_of_schrodinger
    q ℏ mass (vectorPotential x) vectorPotentialDerivative scalarPotential
    (ψSpace x) ψt (ψx x) ψxx hℏ hmass hschrodinger, mul_zero]

end
end Continuum
end SingleParticle
end QuantumMechanics
