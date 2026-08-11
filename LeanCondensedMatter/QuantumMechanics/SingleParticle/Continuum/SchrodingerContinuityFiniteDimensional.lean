import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerContinuity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Pointwise Schrödinger continuity equation in finite spatial dimension

This module assembles the one-dimensional pointwise current identity coordinate by coordinate.
For spatial dimension `d`, the gradient and diagonal Hessian values are represented by families
indexed by `Fin d`. The divergence and Laplacian are their finite coordinate sums.

The theorem remains pointwise: it assumes coordinate-line derivatives through one spacetime point.
It does not identify the Laplacian with a bounded operator on `L²`, and it does not hide Sobolev or
operator-domain assumptions.
-/

namespace QuantumTheory
namespace Continuum

noncomputable section

open scoped BigOperators

/-- Pointwise probability-current vector in `d` spatial dimensions. -/
def probabilityCurrentValue {d : ℕ} (ℏ κ : ℝ) (ψ : ℂ)
    (gradient : Fin d → ℂ) : Fin d → ℝ :=
  fun i => probabilityCurrentValue1D ℏ κ ψ (gradient i)

@[simp]
theorem probabilityCurrentValue_apply {d : ℕ} (ℏ κ : ℝ) (ψ : ℂ)
    (gradient : Fin d → ℂ) (i : Fin d) :
    probabilityCurrentValue ℏ κ ψ gradient i =
      probabilityCurrentValue1D ℏ κ ψ (gradient i) :=
  rfl

/-- Pointwise divergence assembled from the diagonal second spatial derivatives. -/
def probabilityCurrentDivergenceValue {d : ℕ} (ℏ κ : ℝ) (ψ : ℂ)
    (secondDerivatives : Fin d → ℂ) : ℝ :=
  ∑ i, probabilityCurrentDivergenceValue1D ℏ κ ψ (secondDerivatives i)

/-- The one-dimensional current-divergence value is additive in the second derivative. -/
theorem probabilityCurrentDivergenceValue1D_add
    (ℏ κ : ℝ) (ψ a b : ℂ) :
    probabilityCurrentDivergenceValue1D ℏ κ ψ (a + b) =
      probabilityCurrentDivergenceValue1D ℏ κ ψ a +
        probabilityCurrentDivergenceValue1D ℏ κ ψ b := by
  change
    (2 * κ / ℏ) * (ψ.re * (a + b).im - ψ.im * (a + b).re) =
      (2 * κ / ℏ) * (ψ.re * a.im - ψ.im * a.re) +
        (2 * κ / ℏ) * (ψ.re * b.im - ψ.im * b.re)
  simp
  ring

/-- The one-dimensional current-divergence value vanishes at zero second derivative. -/
theorem probabilityCurrentDivergenceValue1D_zero
    (ℏ κ : ℝ) (ψ : ℂ) :
    probabilityCurrentDivergenceValue1D ℏ κ ψ 0 = 0 := by
  change (2 * κ / ℏ) * (ψ.re * (0 : ℂ).im - ψ.im * (0 : ℂ).re) = 0
  simp

/-- Finite coordinate sums commute with the pointwise current-divergence value. -/
theorem probabilityCurrentDivergenceValue1D_sum
    {ι : Type*} (s : Finset ι) (ℏ κ : ℝ) (ψ : ℂ) (f : ι → ℂ) :
    probabilityCurrentDivergenceValue1D ℏ κ ψ (∑ i ∈ s, f i) =
      ∑ i ∈ s, probabilityCurrentDivergenceValue1D ℏ κ ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [probabilityCurrentDivergenceValue1D_zero]
  | @insert a s ha ih =>
      simp [ha, probabilityCurrentDivergenceValue1D_add, ih]

/-- The coordinate divergence equals the one-dimensional divergence formula evaluated on the
pointwise Laplacian value `∑ i, ∂ᵢ²ψ`. -/
theorem probabilityCurrentDivergenceValue_eq_laplacian
    {d : ℕ} (ℏ κ : ℝ) (ψ : ℂ) (secondDerivatives : Fin d → ℂ) :
    probabilityCurrentDivergenceValue ℏ κ ψ secondDerivatives =
      probabilityCurrentDivergenceValue1D ℏ κ ψ (∑ i, secondDerivatives i) := by
  unfold probabilityCurrentDivergenceValue
  symm
  simpa using probabilityCurrentDivergenceValue1D_sum
    (s := Finset.univ) ℏ κ ψ secondDerivatives

/-- Pointwise finite-dimensional probability balance from the scalar-potential Schrödinger equation.

The complex number `∑ i, secondDerivatives i` is the pointwise Laplacian value. -/
theorem finiteDimensional_probability_continuity_balance_of_schrodinger
    {d : ℕ} (ℏ κ potential : ℝ) (ψ ψt : ℂ)
    (secondDerivatives : Fin d → ℂ) (hℏ : ℏ ≠ 0)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        -(κ : ℂ) * (∑ i, secondDerivatives i) + (potential : ℂ) * ψ) :
    probabilityDensityTimeDerivativeValue ψ ψt +
      probabilityCurrentDivergenceValue ℏ κ ψ secondDerivatives = 0 := by
  rw [probabilityCurrentDivergenceValue_eq_laplacian]
  exact probability_continuity_balance_of_schrodinger
    ℏ κ potential ψ ψt (∑ i, secondDerivatives i) hℏ hschrodinger

/-- Pointwise finite-dimensional continuity equation assembled from coordinate-line derivatives.

For each coordinate `i`, `ψSpace i` is the restriction of the wavefunction to the coordinate line
through the selected spatial point, and `ψx i` is its first spatial derivative along that line.
The family `secondDerivatives` contains the diagonal second derivatives at the point. The conclusion
is the coordinate expression

`∂ₜρ + ∑ i, ∂ᵢjᵢ = 0`.
-/
theorem finiteDimensional_schrodinger_continuity
    {d : ℕ} (ℏ κ potential : ℝ) (hℏ : ℏ ≠ 0)
    {ψTime : ℝ → ℂ} {ψSpace ψx : Fin d → ℝ → ℂ}
    {ψt : ℂ} {secondDerivatives : Fin d → ℂ}
    {t : ℝ} {x : Fin d → ℝ}
    (hsame : ∀ i, ψSpace i (x i) = ψTime t)
    (htimeRe : HasDerivAt (fun s => (ψTime s).re) ψt.re t)
    (htimeIm : HasDerivAt (fun s => (ψTime s).im) ψt.im t)
    (hspaceRe : ∀ i,
      HasDerivAt (fun y => (ψSpace i y).re) (ψx i (x i)).re (x i))
    (hspaceIm : ∀ i,
      HasDerivAt (fun y => (ψSpace i y).im) (ψx i (x i)).im (x i))
    (hspaceDerivativeRe : ∀ i,
      HasDerivAt (fun y => (ψx i y).re) (secondDerivatives i).re (x i))
    (hspaceDerivativeIm : ∀ i,
      HasDerivAt (fun y => (ψx i y).im) (secondDerivatives i).im (x i))
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        -(κ : ℂ) * (∑ i, secondDerivatives i) +
          (potential : ℂ) * ψTime t) :
    deriv (fun s => probabilityDensityValue (ψTime s)) t +
      ∑ i, deriv
        (fun y => probabilityCurrentValue1D ℏ κ (ψSpace i y) (ψx i y)) (x i) = 0 := by
  rw [(hasDerivAt_probabilityDensityValue htimeRe htimeIm).deriv]
  have hcurrent (i : Fin d) :
      deriv (fun y => probabilityCurrentValue1D ℏ κ (ψSpace i y) (ψx i y)) (x i) =
        probabilityCurrentDivergenceValue1D ℏ κ (ψTime t) (secondDerivatives i) := by
    rw [(hasDerivAt_probabilityCurrentValue1D ℏ κ
      (hspaceRe i) (hspaceIm i) (hspaceDerivativeRe i) (hspaceDerivativeIm i)).deriv]
    rw [hsame i]
  rw [Finset.sum_congr rfl (fun i _ => hcurrent i)]
  exact finiteDimensional_probability_continuity_balance_of_schrodinger
    ℏ κ potential (ψTime t) ψt secondDerivatives hℏ hschrodinger

/-- Pointwise charge-current vector obtained by scaling probability current by the particle charge. -/
def chargeCurrentValue {d : ℕ} (q ℏ κ : ℝ) (ψ : ℂ)
    (gradient : Fin d → ℂ) : Fin d → ℝ :=
  fun i => q * probabilityCurrentValue ℏ κ ψ gradient i

@[simp]
theorem chargeCurrentValue_apply {d : ℕ} (q ℏ κ : ℝ) (ψ : ℂ)
    (gradient : Fin d → ℂ) (i : Fin d) :
    chargeCurrentValue q ℏ κ ψ gradient i =
      q * probabilityCurrentValue1D ℏ κ ψ (gradient i) :=
  rfl

end
end Continuum
end QuantumTheory
