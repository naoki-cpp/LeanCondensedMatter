import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerGaugeCurrent1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerContinuity
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerMinimalCoupling1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Gauge-covariant Schrödinger continuity equation in one dimension

This module derives the pointwise electromagnetic probability and charge continuity equations from
the minimal-coupling algebra in `SchrodingerMinimalCoupling1D` and the current in
`SchrodingerGaugeCurrent1D`.

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

/-- Expanded form of the electromagnetic current divergence. -/
theorem electromagneticProbabilityCurrentDivergenceValue1D_eq_expanded
    (q ℏ mass vectorPotential vectorPotentialDerivative : ℝ)
    (ψ ψx ψxx : ℂ) :
    electromagneticProbabilityCurrentDivergenceValue1D
        q ℏ mass vectorPotential vectorPotentialDerivative ψ ψx ψxx =
      (ℏ / mass) * (ψ.re * ψxx.im - ψ.im * ψxx.re) -
        (q / mass) * vectorPotentialDerivative * probabilityDensityValue ψ -
        (2 * q / mass) * vectorPotential *
          (ψ.re * ψx.re + ψ.im * ψx.im) := by
  unfold electromagneticProbabilityCurrentDivergenceValue1D
  rw [probabilityDensityTimeDerivativeValue_eq_coordinates]
  ring

/-- Differentiating the gauge-covariant current uses the product rule for the vector potential and
for the wavefunction coordinates explicitly. -/
theorem hasDerivAt_electromagneticProbabilityCurrentValue1D
    (q ℏ mass : ℝ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    {vectorPotential : ℝ → ℝ} {vectorPotentialDerivative : ℝ}
    {ψ ψx : ℝ → ℂ} {ψxx : ℂ} {x : ℝ}
    (hA : HasDerivAt vectorPotential vectorPotentialDerivative x)
    (hψre : HasDerivAt (fun y => (ψ y).re) (ψx x).re x)
    (hψim : HasDerivAt (fun y => (ψ y).im) (ψx x).im x)
    (hψxre : HasDerivAt (fun y => (ψx y).re) ψxx.re x)
    (hψxim : HasDerivAt (fun y => (ψx y).im) ψxx.im x) :
    HasDerivAt
      (fun y => electromagneticProbabilityCurrentValue1D
        q ℏ mass (vectorPotential y) (ψ y) (ψx y))
      (electromagneticProbabilityCurrentDivergenceValue1D
        q ℏ mass (vectorPotential x) vectorPotentialDerivative (ψ x) (ψx x) ψxx) x := by
  have hpairRaw := HasDerivAt.sub
    (HasDerivAt.mul hψre hψxim) (HasDerivAt.mul hψim hψxre)
  have hderiv :
      ((ψx x).re * (ψx x).im + (ψ x).re * ψxx.im) -
          ((ψx x).im * (ψx x).re + (ψ x).im * ψxx.re) =
        (ψ x).re * ψxx.im - (ψ x).im * ψxx.re := by
    ring
  rw [hderiv] at hpairRaw
  have hpair :
      HasDerivAt
        (fun y => (ψ y).re * (ψx y).im - (ψ y).im * (ψx y).re)
        ((ψ x).re * ψxx.im - (ψ x).im * ψxx.re) x := by
    rw [hasDerivAt_iff_tendsto]
    rw [hasDerivAt_iff_tendsto] at hpairRaw
    simpa [Pi.mul_apply, Pi.sub_apply] using hpairRaw
  have hparamagnetic := hpair.const_mul (ℏ / mass)
  have hdensity := hasDerivAt_probabilityDensityValue hψre hψim
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

/-- Real and imaginary component equations of the minimally coupled Schrödinger equation, written
without denominators after multiplication by `2m`. -/
theorem electromagnetic_schrodinger_component_equations
    (q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential : ℝ)
    (ψ ψt ψx ψxx : ℂ) (hmass : mass ≠ 0)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential ψ ψx ψxx) :
    2 * mass * ℏ * ψt.im =
        ℏ ^ 2 * ψxx.re + 2 * q * ℏ * vectorPotential * ψx.im +
          q * ℏ * vectorPotentialDerivative * ψ.im -
          (q ^ 2 * vectorPotential ^ 2 + 2 * mass * q * scalarPotential) * ψ.re ∧
      2 * mass * ℏ * ψt.re =
        -(ℏ ^ 2 * ψxx.im) + 2 * q * ℏ * vectorPotential * ψx.re +
          q * ℏ * vectorPotentialDerivative * ψ.re +
          (q ^ 2 * vectorPotential ^ 2 + 2 * mass * q * scalarPotential) * ψ.im := by
  let kineticCoefficient : ℝ := ℏ ^ 2 / (2 * mass)
  let vectorPotentialCoefficient : ℝ := q * ℏ * vectorPotential / mass
  let vectorPotentialDerivativeCoefficient : ℝ :=
    q * ℏ * vectorPotentialDerivative / (2 * mass)
  let scalarCoefficient : ℝ :=
    q ^ 2 * vectorPotential ^ 2 / (2 * mass) + q * scalarPotential
  have hexpanded :
      minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential ψ ψx ψxx =
        -((kineticCoefficient : ℝ) : ℂ) * ψxx +
          Complex.I * ((vectorPotentialCoefficient : ℝ) : ℂ) * ψx +
          Complex.I * ((vectorPotentialDerivativeCoefficient : ℝ) : ℂ) * ψ +
          ((scalarCoefficient : ℝ) : ℂ) * ψ := by
    simpa [kineticCoefficient, vectorPotentialCoefficient,
      vectorPotentialDerivativeCoefficient, scalarCoefficient] using
      (minimallyCoupledSchrodingerRhsValue1D_eq_expanded
        q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential ψ ψx ψxx hmass)
  rw [hexpanded] at hschrodinger
  have hreRaw := congrArg Complex.re hschrodinger
  have himRaw := congrArg Complex.im hschrodinger
  have hre :
      -(ℏ * ψt.im) =
        -kineticCoefficient * ψxx.re -
          vectorPotentialCoefficient * ψx.im -
          vectorPotentialDerivativeCoefficient * ψ.im +
          scalarCoefficient * ψ.re := by
    simpa [sub_eq_add_neg] using hreRaw
  have him :
      ℏ * ψt.re =
        -kineticCoefficient * ψxx.im +
          vectorPotentialCoefficient * ψx.re +
          vectorPotentialDerivativeCoefficient * ψ.re +
          scalarCoefficient * ψ.im := by
    simpa using himRaw
  dsimp [kineticCoefficient, vectorPotentialCoefficient,
    vectorPotentialDerivativeCoefficient, scalarCoefficient] at hre him
  field_simp [hmass] at hre him
  constructor
  · linear_combination -hre
  · linear_combination him

/-- The local probability balance from the electromagnetic component equations. -/
theorem electromagnetic_probability_continuity_balance_of_components
    (q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential : ℝ)
    (ψ ψt ψx ψxx : ℂ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    (hreal :
      2 * mass * ℏ * ψt.im =
        ℏ ^ 2 * ψxx.re + 2 * q * ℏ * vectorPotential * ψx.im +
          q * ℏ * vectorPotentialDerivative * ψ.im -
          (q ^ 2 * vectorPotential ^ 2 + 2 * mass * q * scalarPotential) * ψ.re)
    (himag :
      2 * mass * ℏ * ψt.re =
        -(ℏ ^ 2 * ψxx.im) + 2 * q * ℏ * vectorPotential * ψx.re +
          q * ℏ * vectorPotentialDerivative * ψ.re +
          (q ^ 2 * vectorPotential ^ 2 + 2 * mass * q * scalarPotential) * ψ.im) :
    probabilityDensityTimeDerivativeValue ψ ψt +
      electromagneticProbabilityCurrentDivergenceValue1D
        q ℏ mass vectorPotential vectorPotentialDerivative ψ ψx ψxx = 0 := by
  have hscaled :
      ℏ * (probabilityDensityTimeDerivativeValue ψ ψt +
        electromagneticProbabilityCurrentDivergenceValue1D
          q ℏ mass vectorPotential vectorPotentialDerivative ψ ψx ψxx) = 0 := by
    rw [electromagneticProbabilityCurrentDivergenceValue1D_eq_expanded,
      probabilityDensityTimeDerivativeValue_eq_coordinates,
      probabilityDensityValue, Complex.normSq_apply]
    field_simp [hmass]
    linear_combination ψ.re * himag + ψ.im * hreal
  exact (mul_eq_zero.mp hscaled).resolve_left hℏ

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
  rcases electromagnetic_schrodinger_component_equations
      q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential
      ψ ψt ψx ψxx hmass hschrodinger with ⟨hreal, himag⟩
  exact electromagnetic_probability_continuity_balance_of_components
    q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential
    ψ ψt ψx ψxx hℏ hmass hreal himag

/-- One-dimensional pointwise electromagnetic Schrödinger continuity equation. All time, space,
and vector-potential derivatives used in the proof are explicit hypotheses. -/
theorem oneDimensional_electromagnetic_schrodinger_continuity
    (q ℏ mass scalarPotential : ℝ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    {ψTime ψSpace ψx : ℝ → ℂ} {vectorPotential : ℝ → ℝ}
    {ψt ψxx : ℂ} {vectorPotentialDerivative : ℝ} {t x : ℝ}
    (hsame : ψTime t = ψSpace x)
    (htimeRe : HasDerivAt (fun s => (ψTime s).re) ψt.re t)
    (htimeIm : HasDerivAt (fun s => (ψTime s).im) ψt.im t)
    (hspaceRe : HasDerivAt (fun y => (ψSpace y).re) (ψx x).re x)
    (hspaceIm : HasDerivAt (fun y => (ψSpace y).im) (ψx x).im x)
    (hspaceDerivativeRe : HasDerivAt (fun y => (ψx y).re) ψxx.re x)
    (hspaceDerivativeIm : HasDerivAt (fun y => (ψx y).im) ψxx.im x)
    (hvectorPotential : HasDerivAt vectorPotential vectorPotentialDerivative x)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass (vectorPotential x) vectorPotentialDerivative scalarPotential
          (ψSpace x) (ψx x) ψxx) :
    deriv (fun s => probabilityDensityValue (ψTime s)) t +
      deriv (fun y => electromagneticProbabilityCurrentValue1D
        q ℏ mass (vectorPotential y) (ψSpace y) (ψx y)) x = 0 := by
  rw [(hasDerivAt_probabilityDensityValue htimeRe htimeIm).deriv,
    (hasDerivAt_electromagneticProbabilityCurrentValue1D
      q ℏ mass hℏ hmass hvectorPotential hspaceRe hspaceIm
      hspaceDerivativeRe hspaceDerivativeIm).deriv]
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
    (htimeRe : HasDerivAt (fun s => (ψTime s).re) ψt.re t)
    (htimeIm : HasDerivAt (fun s => (ψTime s).im) ψt.im t)
    (hspaceRe : HasDerivAt (fun y => (ψSpace y).re) (ψx x).re x)
    (hspaceIm : HasDerivAt (fun y => (ψSpace y).im) (ψx x).im x)
    (hspaceDerivativeRe : HasDerivAt (fun y => (ψx y).re) ψxx.re x)
    (hspaceDerivativeIm : HasDerivAt (fun y => (ψx y).im) ψxx.im x)
    (hvectorPotential : HasDerivAt vectorPotential vectorPotentialDerivative x)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass (vectorPotential x) vectorPotentialDerivative scalarPotential
          (ψSpace x) (ψx x) ψxx) :
    deriv (fun s => chargeDensityValue q (ψTime s)) t +
      deriv (fun y => electromagneticChargeCurrentValue1D
        q ℏ mass (vectorPotential y) (ψSpace y) (ψx y)) x = 0 := by
  have hdensity := hasDerivAt_probabilityDensityValue htimeRe htimeIm
  have hcurrent := hasDerivAt_electromagneticProbabilityCurrentValue1D
    q ℏ mass hℏ hmass hvectorPotential hspaceRe hspaceIm
    hspaceDerivativeRe hspaceDerivativeIm
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
  rw [hchargeDensity.deriv, hchargeCurrent.deriv]
  apply charge_continuity_balance_of_probability
  rw [hsame]
  exact electromagnetic_probability_continuity_balance_of_schrodinger
    q ℏ mass (vectorPotential x) vectorPotentialDerivative scalarPotential
    (ψSpace x) ψt (ψx x) ψxx hℏ hmass hschrodinger

end
end Continuum
end SingleParticle
end QuantumMechanics