import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerGaugeCurrent1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Gauge-covariant Schrödinger continuity equation in one dimension

This module extends the pointwise scalar-potential continuity equation to electromagnetic minimal
coupling.  The vector potential and its spatial derivative are explicit theorem inputs.  No magnetic
operator on `L²` or self-adjointness statement is introduced here.

For the convention

`π_A = -iℏ ∂ₓ - q A`,

we first expand `π_A² ψ`, including the derivative of `A`, and then derive the local probability and
charge continuity equations from

`iℏ ψₜ = (1 / (2m)) π_A² ψ + q φ ψ`.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

/-- The value obtained by differentiating `(-iℏ ∂ₓ - q A) ψ` once in space, with `Aₓ`, `ψₓ`, and
`ψₓₓ` supplied explicitly. -/
def kineticMomentumDerivativeValue1D
    (q ℏ vectorPotential vectorPotentialDerivative : ℝ) (ψ ψx ψxx : ℂ) : ℂ :=
  -(Complex.I * (ℏ : ℂ)) * ψxx -
    ((q * vectorPotentialDerivative : ℝ) : ℂ) * ψ -
    ((q * vectorPotential : ℝ) : ℂ) * ψx

/-- Pointwise value of `(-iℏ ∂ₓ - q A)² ψ`, with the derivative of the first momentum value supplied
by `kineticMomentumDerivativeValue1D`. -/
def kineticMomentumSquaredValue1D
    (q ℏ vectorPotential vectorPotentialDerivative : ℝ) (ψ ψx ψxx : ℂ) : ℂ :=
  kineticMomentumValue1D q ℏ vectorPotential
    (kineticMomentumValue1D q ℏ vectorPotential ψ ψx)
    (kineticMomentumDerivativeValue1D q ℏ vectorPotential vectorPotentialDerivative ψ ψx ψxx)

/-- Expanding the minimally coupled kinetic momentum square gives the Laplacian term, the two
vector-potential derivative terms, and the `q² A²` term. -/
theorem kineticMomentumSquaredValue1D_eq_expanded
    (q ℏ vectorPotential vectorPotentialDerivative : ℝ) (ψ ψx ψxx : ℂ) :
    kineticMomentumSquaredValue1D q ℏ vectorPotential vectorPotentialDerivative ψ ψx ψxx =
      -((ℏ ^ 2 : ℝ) : ℂ) * ψxx +
        Complex.I * ((q * ℏ * vectorPotentialDerivative : ℝ) : ℂ) * ψ +
        2 * Complex.I * ((q * ℏ * vectorPotential : ℝ) : ℂ) * ψx +
        ((q ^ 2 * vectorPotential ^ 2 : ℝ) : ℂ) * ψ := by
  apply Complex.ext
  · simp [kineticMomentumSquaredValue1D, kineticMomentumDerivativeValue1D,
      kineticMomentumValue1D, pow_two]; ring
  · simp [kineticMomentumSquaredValue1D, kineticMomentumDerivativeValue1D,
      kineticMomentumValue1D, pow_two]; ring

/-- The free kinetic coefficient `ℏ² / (2m)` occurring after minimal-coupling expansion. -/
def electromagneticKineticCoefficient1D (ℏ mass : ℝ) : ℝ :=
  ℏ ^ 2 / (2 * mass)

/-- Coefficient of the `i A ψₓ` term in the expanded minimal-coupling Hamiltonian. -/
def electromagneticVectorPotentialCoefficient1D
    (q ℏ mass vectorPotential : ℝ) : ℝ :=
  q * ℏ * vectorPotential / mass

/-- Coefficient of the `i Aₓ ψ` term in the expanded minimal-coupling Hamiltonian. -/
def electromagneticVectorPotentialDerivativeCoefficient1D
    (q ℏ mass vectorPotentialDerivative : ℝ) : ℝ :=
  q * ℏ * vectorPotentialDerivative / (2 * mass)

/-- Real multiplication coefficient collecting the `A²` and scalar-potential terms. -/
def electromagneticScalarCoefficient1D
    (q mass vectorPotential scalarPotential : ℝ) : ℝ :=
  q ^ 2 * vectorPotential ^ 2 / (2 * mass) + q * scalarPotential

/-- The pointwise right-hand side of the minimally coupled Schrödinger equation
`(1 / (2m)) π_A² ψ + q φ ψ`. -/
def minimallyCoupledSchrodingerRhsValue1D
    (q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential : ℝ)
    (ψ ψx ψxx : ℂ) : ℂ :=
  (((1 / (2 * mass) : ℝ) : ℂ) *
      kineticMomentumSquaredValue1D q ℏ vectorPotential vectorPotentialDerivative ψ ψx ψxx) +
    ((q * scalarPotential : ℝ) : ℂ) * ψ

/-- Explicit expansion of the minimally coupled Schrödinger right-hand side. -/
theorem minimallyCoupledSchrodingerRhsValue1D_eq_expanded
    (q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential : ℝ)
    (ψ ψx ψxx : ℂ) (hmass : mass ≠ 0) :
    minimallyCoupledSchrodingerRhsValue1D
        q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential ψ ψx ψxx =
      -((electromagneticKineticCoefficient1D ℏ mass : ℝ) : ℂ) * ψxx +
        Complex.I *
          ((electromagneticVectorPotentialCoefficient1D q ℏ mass vectorPotential : ℝ) : ℂ) * ψx +
        Complex.I *
          ((electromagneticVectorPotentialDerivativeCoefficient1D
            q ℏ mass vectorPotentialDerivative : ℝ) : ℂ) * ψ +
        ((electromagneticScalarCoefficient1D q mass vectorPotential scalarPotential : ℝ) : ℂ) * ψ := by
  have hmassC : (mass : ℂ) ≠ 0 := by
    exact_mod_cast hmass
  unfold minimallyCoupledSchrodingerRhsValue1D electromagneticKineticCoefficient1D
    electromagneticVectorPotentialCoefficient1D
    electromagneticVectorPotentialDerivativeCoefficient1D electromagneticScalarCoefficient1D
  rw [kineticMomentumSquaredValue1D_eq_expanded]
  push_cast
  field_simp [hmassC]; ring

private theorem probabilityDensityValue_eq_coordinates (ψ : ℂ) :
    probabilityDensityValue ψ = ψ.re ^ 2 + ψ.im ^ 2 :=
  rfl

private theorem probabilityDensityTimeDerivativeValue_eq_coordinates (ψ ψd : ℂ) :
    probabilityDensityTimeDerivativeValue ψ ψd =
      2 * (ψ.re * ψd.re + ψ.im * ψd.im) :=
  rfl

/-- The value obtained by differentiating the electromagnetic probability current in space.  The
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
  rw [minimallyCoupledSchrodingerRhsValue1D_eq_expanded
    q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential ψ ψx ψxx hmass]
    at hschrodinger
  have hreRaw := congrArg Complex.re hschrodinger
  have himRaw := congrArg Complex.im hschrodinger
  have hre :
      -(ℏ * ψt.im) =
        -electromagneticKineticCoefficient1D ℏ mass * ψxx.re -
          electromagneticVectorPotentialCoefficient1D q ℏ mass vectorPotential * ψx.im -
          electromagneticVectorPotentialDerivativeCoefficient1D
            q ℏ mass vectorPotentialDerivative * ψ.im +
          electromagneticScalarCoefficient1D
            q mass vectorPotential scalarPotential * ψ.re := by
    simpa [sub_eq_add_neg] using hreRaw
  have him :
      ℏ * ψt.re =
        -electromagneticKineticCoefficient1D ℏ mass * ψxx.im +
          electromagneticVectorPotentialCoefficient1D q ℏ mass vectorPotential * ψx.re +
          electromagneticVectorPotentialDerivativeCoefficient1D
            q ℏ mass vectorPotentialDerivative * ψ.re +
          electromagneticScalarCoefficient1D
            q mass vectorPotential scalarPotential * ψ.im := by
    simpa using himRaw
  unfold electromagneticKineticCoefficient1D electromagneticVectorPotentialCoefficient1D
    electromagneticVectorPotentialDerivativeCoefficient1D electromagneticScalarCoefficient1D
    at hre him
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
      probabilityDensityValue_eq_coordinates]
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

/-- One-dimensional pointwise electromagnetic Schrödinger continuity equation.  All time, space,
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
