import LeanCondensedMatter.Transport.Analysis.BesselYFormalCoefficients
import Mathlib.Tactic.Omega

set_option linter.style.header false

/-!
# Formal Y₁ coefficients and the exact normalized harmonic Wronskian

The order-one correction of the concrete DLMF Y₁ series
is represented by the formal power series

  C(x) = Σ (Hₙ + Hₙ₊₁) xⁿ / (n!(n+1)!).

The harmonic recurrence gives a formal derivative relation

  x C = 2x B' - (A-1),

where A(x)=Σ xⁿ/(n!)² and B(x)=Σ Hₙxⁿ/(n!)²
are the concrete formal series from BesselYFormalCoefficients.

Inserting this relation into the proved Frobenius invariant
A²+2x(A'B-AB')=1 yields

  A+2x A'B-x A C=1.

After the analytic evaluation at x=-z²/4, this is exactly
the remaining complex Bessel J/Y harmonic-series identity
of PR #4529. The formal identity is unconditional;
passing to analytic sums needs a separate justified
evaluation/Cauchy product theorem, not an assertion.
-/

namespace QuantumTheory.Transport

noncomputable section

open scoped PowerSeries

/-- Exact order-one harmonic correction as a **formal**
power series with DLMF coefficients. -/
noncomputable def besselFormalH1 : ℂ⟦X⟧ :=
  PowerSeries.mk fun n : ℕ =>
    ((harmonic n : ℂ) + (harmonic (n + 1) : ℂ)) /
      ((n.factorial : ℂ) * ((n + 1).factorial : ℂ))

/-- The single coefficient identity linking order-one harmonic
corrections to the derivative of the order-zero correction. -/
theorem besselFormalH1_coeff (n : ℕ) :
    PowerSeries.coeff n besselFormalH1 =
      2 * ((n + 1 : ℕ) : ℂ) *
          PowerSeries.coeff (n + 1) besselFormalH0 -
        PowerSeries.coeff (n + 1) besselFormalJ0 := by
  simp only [besselFormalH1, besselFormalH0, besselFormalJ0,
    PowerSeries.coeff_mk]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hH : (harmonic (n + 1) : ℂ) =
      (harmonic n : ℂ) + (((n + 1 : ℕ) : ℂ))⁻¹ := by
    rw [harmonic_succ]
    push_cast
    rfl
  rw [hH, Nat.factorial_succ]
  push_cast
  field_simp [hn, hf] <;> ring

/-- Precise formal derivative relation behind the order-one
DLMF harmonic correction; no differentiation of a complex
infinite sum is used. -/
theorem besselFormalH1_derivative_relation :
    PowerSeries.X * besselFormalH1 =
      PowerSeries.X * (2 * PowerSeries.derivative besselFormalH0) -
        (besselFormalJ0 - 1) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [besselFormalJ0_constantCoeff,
      PowerSeries.coeff_zero_X_mul]
  | succ n =>
    simp only [map_sub, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_derivative]
    simp only [PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, sub_zero]
    simpa only [mul_assoc] using (besselFormalH1_coeff n)

/-- Formal version of the actual Wronskian-reducing identity,
now **unconditionally proved** for the factorial/harmonic
coefficient sequences defining J₀, Y₀ and Y₁.
Analytic evaluation remains separate. -/
theorem besselFormalJ0H0H1_harmonicIdentity :
    besselFormalJ0 +
        PowerSeries.X *
          (2 * PowerSeries.derivative besselFormalJ0 * besselFormalH0) -
        PowerSeries.X * (besselFormalJ0 * besselFormalH1) = 1 := by
  have hW := besselFormalJ0H0_wronskian
  have hC := besselFormalH1_derivative_relation
  unfold besselFormalWronskianInvariant at hW
  linear_combination hW - besselFormalJ0 * hC

end

end QuantumTheory.Transport
