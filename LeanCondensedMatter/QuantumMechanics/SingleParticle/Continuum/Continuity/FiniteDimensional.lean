import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.Scalar1D
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Module

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

namespace QuantumMechanics
namespace SingleParticle
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

/-- The coordinate divergence equals the one-dimensional divergence formula evaluated on the
pointwise Laplacian value `∑ i, ∂ᵢ²ψ`. -/
theorem probabilityCurrentDivergenceValue_eq_laplacian
    {d : ℕ} (ℏ κ : ℝ) (ψ : ℂ) (secondDerivatives : Fin d → ℂ) :
    probabilityCurrentDivergenceValue ℏ κ ψ secondDerivatives =
      probabilityCurrentDivergenceValue1D ℏ κ ψ (∑ i, secondDerivatives i) := by
  simp only [probabilityCurrentDivergenceValue,
    probabilityCurrentDivergenceValue1D_eq_coordinates, Complex.re_sum, Complex.im_sum,
    Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]

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
    (htime : HasDerivAt ψTime ψt t)
    (hspace : ∀ i,
      HasDerivAt ψSpace i (ψx i (x i)) (x i))
    (hspaceDerivative : ∀ i,
      HasDerivAt ψx i (secondDerivatives i) (x i))
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        -(κ : ℂ) * (∑ i, secondDerivatives i) +
          (potential : ℂ) * ψTime t) :
    deriv (fun s => probabilityDensityValue (ψTime s)) t +
      ∑ i, deriv
        (fun y => probabilityCurrentValue1D ℏ κ (ψSpace i y) (ψx i y)) (x i) = 0 := by
  rw [(hasDerivAt_probabilityDensityValue htime).deriv]
  have hcurrent (i : Fin d) :
      deriv (fun y => probabilityCurrentValue1D ℏ κ (ψSpace i y) (ψx i y)) (x i) =
        probabilityCurrentDivergenceValue1D ℏ κ (ψTime t) (secondDerivatives i) := by
    rw [(hasDerivAt_probabilityCurrentValue1D ℏ κ
      (hspace i) (hspaceDerivative i)).deriv]
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
end SingleParticle
end QuantumMechanics
