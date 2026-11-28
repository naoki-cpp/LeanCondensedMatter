import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Probability.Basic1D
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Pointwise Schrödinger continuity equation in one space dimension

This module derives the local probability-current balance from the scalar-potential
nonrelativistic Schrödinger equation without treating the Laplacian as a bounded operator on `L²`.
The dynamics-independent probability density, current pairing, current, and charge quantities live
in `Probability/Basic1D`; this module owns their derivative identities and the Schrödinger-specific
cancellation.

Write the kinetic coefficient as `κ = ℏ² / (2m)`. At one spacetime point the Schrödinger equation is

`i ℏ ψₜ = -κ ψₓₓ + V ψ`,

where `V : ℝ`. Probability density and current are real-valued:

`ρ = |ψ|²`,
`j = (2κ / ℏ) Im (star ψ * ψₓ)`.

After substituting `κ = ℏ² / (2m)`, the current is the standard
`(ℏ / m) Im (star ψ * ψₓ)`. Keeping `κ` explicit makes the local cancellation independent of the
later mass parametrization.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

/-- The value obtained by differentiating probability density in time. -/
def probabilityDensityTimeDerivativeValue (ψ ψt : ℂ) : ℝ :=
  2 * (ψ.re * ψt.re + ψ.im * ψt.im)

/-- Coordinate expansion of the probability-density time derivative. -/
theorem probabilityDensityTimeDerivativeValue_eq_coordinates (ψ ψt : ℂ) :
    probabilityDensityTimeDerivativeValue ψ ψt =
      2 * (ψ.re * ψt.re + ψ.im * ψt.im) := by
  rfl

/-- The value obtained by differentiating the one-dimensional probability current in space. -/
def probabilityCurrentDivergenceValue1D (ℏ κ : ℝ) (ψ ψxx : ℂ) : ℝ :=
  (2 * κ / ℏ) * probabilityCurrentPairingValue ψ ψxx

/-- Coordinate expansion of the one-dimensional probability-current divergence. -/
theorem probabilityCurrentDivergenceValue1D_eq_coordinates
    (ℏ κ : ℝ) (ψ ψxx : ℂ) :
    probabilityCurrentDivergenceValue1D ℏ κ ψ ψxx =
      (2 * κ / ℏ) * (ψ.re * ψxx.im - ψ.im * ψxx.re) := by
  rw [probabilityCurrentDivergenceValue1D, probabilityCurrentPairingValue_eq_coordinates]

/-- Real differentiation of a complex wavefunction gives the probability-density derivative. -/
theorem hasDerivAt_probabilityDensityValue
    {ψ : ℝ → ℂ} {ψt : ℂ} {t : ℝ}
    (hψ : HasDerivAt ψ ψt t) :
    HasDerivAt (fun s => probabilityDensityValue (ψ s))
      (probabilityDensityTimeDerivativeValue (ψ t) ψt) t := by
  have hconj : HasDerivAt (fun s => star (ψ s)) (star ψt) t :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt t hψ
  have hraw : HasDerivAt (fun s => (ψ s * star (ψ s)).re)
      (ψt * star (ψ t) + ψ t * star ψt).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hψ.mul hconj)
  have hvalue : (ψt * star (ψ t) + ψ t * star ψt).re =
      probabilityDensityTimeDerivativeValue (ψ t) ψt := by
    simp only [Complex.star_def, Complex.add_re, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, probabilityDensityTimeDerivativeValue]
    ring
  rw [hvalue] at hraw
  simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    probabilityDensityValue] using hraw

/-- Differentiating the standard one-dimensional current cancels the two mixed first-derivative
terms, leaving only the second spatial derivative. -/
theorem hasDerivAt_probabilityCurrentValue1D
    (ℏ κ : ℝ) {ψ ψx : ℝ → ℂ} {ψxx : ℂ} {x : ℝ}
    (hψ : HasDerivAt ψ (ψx x) x)
    (hψx : HasDerivAt ψx ψxx x) :
    HasDerivAt (fun y => probabilityCurrentValue1D ℏ κ (ψ y) (ψx y))
      (probabilityCurrentDivergenceValue1D ℏ κ (ψ x) ψxx) x := by
  have hconj : HasDerivAt (fun y => star (ψ y)) (star (ψx x)) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt x hψ
  have hpair : HasDerivAt (fun y => (star (ψ y) * ψx y).im)
      (star (ψx x) * ψx x + star (ψ x) * ψxx).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hconj.mul hψx)
  have hzero : (star (ψx x) * ψx x).im = 0 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_im]
  rw [Complex.add_im, hzero, zero_add] at hpair
  simpa only [probabilityCurrentValue1D, probabilityCurrentDivergenceValue1D,
    probabilityCurrentPairingValue] using hpair.const_mul (2 * κ / ℏ)

/-- Pointwise continuity balance derived directly from the nonrelativistic Schrödinger equation with
a real scalar potential. -/
theorem probability_continuity_balance_of_schrodinger
    (ℏ κ potential : ℝ) (ψ ψt ψxx : ℂ) (hℏ : ℏ ≠ 0)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt = -(κ : ℂ) * ψxx + (potential : ℂ) * ψ) :
    probabilityDensityTimeDerivativeValue ψ ψt +
      probabilityCurrentDivergenceValue1D ℏ κ ψ ψxx = 0 := by
  have him := congrArg (fun z : ℂ => (star ψ * z).im) hschrodinger
  simp at him
  unfold probabilityDensityTimeDerivativeValue probabilityCurrentDivergenceValue1D
  rw [probabilityCurrentPairingValue_eq_coordinates]
  linear_combination (norm := skip) (2 / ℏ) * him
  field_simp [hℏ]
  ring

/-- One-dimensional pointwise continuity equation for real-differentiable complex time and space
slices of a wavefunction.

The two supplied functions represent the time slice through a fixed spatial point and the spatial
slice at a fixed time. `hsame` identifies their value at the spacetime point under consideration.
No `L²` completion or unbounded-operator assertion is used. -/
theorem oneDimensional_schrodinger_continuity
    (ℏ κ potential : ℝ) (hℏ : ℏ ≠ 0)
    {ψTime ψSpace ψx : ℝ → ℂ} {ψt ψxx : ℂ} {t x : ℝ}
    (hsame : ψTime t = ψSpace x)
    (htime : HasDerivAt ψTime ψt t)
    (hspace : HasDerivAt ψSpace (ψx x) x)
    (hspaceDerivative : HasDerivAt ψx ψxx x)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        -(κ : ℂ) * ψxx + (potential : ℂ) * ψSpace x) :
    deriv (fun s => probabilityDensityValue (ψTime s)) t +
      deriv (fun y => probabilityCurrentValue1D ℏ κ (ψSpace y) (ψx y)) x = 0 := by
  rw [(hasDerivAt_probabilityDensityValue htime).deriv,
    (hasDerivAt_probabilityCurrentValue1D ℏ κ hspace
      hspaceDerivative).deriv]
  rw [hsame]
  exact probability_continuity_balance_of_schrodinger
    ℏ κ potential (ψSpace x) ψt ψxx hℏ hschrodinger

end
end Continuum
end SingleParticle
end QuantumMechanics
