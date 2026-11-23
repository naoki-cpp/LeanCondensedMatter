import LeanCondensedMatter.Analysis.PowerSeries.FrobeniusWronskian
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# Formal Frobenius coefficients for J₀ / Y₀ / Y₁

The factorial coefficient sequence `aₙ=1/(n!)²` and the
harmonic correction sequence `bₙ=Hₙ/(n!)²` realize two
formal power series `A` and `B`.

Their coefficient recurrences are

  (n+1)² aₙ₊₁ = aₙ
  (n+1)² bₙ₊₁ = bₙ + (n+1) aₙ₊₁.

As a result, `A` and `B` satisfy the Frobenius formal
differential equations

  d/dx (x A') = A
  d/dx (x B') = B + A'.

This module works entirely in `ℂ⟦X⟧`, independently of transport or
physical models. Identifying formal evaluation with convergent
analytic Bessel functions and their harmonic `tsum` representations
requires separate theorems in the analytic bridge.
The order-one harmonic correction is formalized in the second section below.
-/

namespace BesselFormal

noncomputable section

open scoped PowerSeries

/-- Zeroth-order Frobenius Bessel-J coefficients. -/
noncomputable def besselFormalJ0 : ℂ⟦X⟧ :=
  PowerSeries.mk fun n : ℕ => (((n.factorial : ℂ) ^ 2))⁻¹

/-- Frobenius harmonic correction coefficients of Bessel Y₀. -/
noncomputable def besselFormalH0 : ℂ⟦X⟧ :=
  PowerSeries.mk fun n : ℕ =>
    (harmonic n : ℂ) / ((n.factorial : ℂ) ^ 2)

/-- The J₀ Frobenius coefficients satisfy the Bessel recurrence
without any convergence assumptions. -/
theorem besselFormalJ0_coeff_succ (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) ^ 2 *
      PowerSeries.coeff (n + 1) besselFormalJ0 =
        PowerSeries.coeff n besselFormalJ0 := by
  simp only [besselFormalJ0, PowerSeries.coeff_mk]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.factorial_succ]
  push_cast
  field_simp [hn, hf]

/-- The harmonic-number recurrence produces the inhomogeneous
Frobenius equation for the Y₀ entire correction. -/
theorem besselFormalH0_coeff_succ (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) ^ 2 *
      PowerSeries.coeff (n + 1) besselFormalH0 =
        PowerSeries.coeff n besselFormalH0 +
          ((n + 1 : ℕ) : ℂ) *
            PowerSeries.coeff (n + 1) besselFormalJ0 := by
  simp only [besselFormalH0, besselFormalJ0, PowerSeries.coeff_mk]
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
  field_simp [hn, hf]

/-- The concrete factorial series solves the homogeneous
order-zero Frobenius equation in the formal power-series ring. -/
theorem besselFormalJ0_frobenius :
    PowerSeries.derivative
      (PowerSeries.X * PowerSeries.derivative besselFormalJ0) =
      besselFormalJ0 := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_derivative,
    PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_derivative]
  calc
    _ = ((n + 1 : ℕ) : ℂ) ^ 2 *
          PowerSeries.coeff (n + 1) besselFormalJ0 := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    _ = _ := besselFormalJ0_coeff_succ n

/-- The concrete harmonic series solves the inhomogeneous
order-zero Frobenius equation in the formal power-series ring. -/
theorem besselFormalH0_frobenius :
    PowerSeries.derivative
      (PowerSeries.X * PowerSeries.derivative besselFormalH0) =
      besselFormalH0 + PowerSeries.derivative besselFormalJ0 := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_derivative,
    PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_derivative]
  have h := besselFormalH0_coeff_succ n
  calc
    _ = ((n + 1 : ℕ) : ℂ) ^ 2 *
        PowerSeries.coeff (n + 1) besselFormalH0 := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    _ = PowerSeries.coeff n besselFormalH0 +
        ((n + 1 : ℕ) : ℂ) *
          PowerSeries.coeff (n + 1) besselFormalJ0 := h
    _ = PowerSeries.coeff n
        (besselFormalH0 + PowerSeries.derivative besselFormalJ0) := by
      simp only [map_add, PowerSeries.coeff_derivative]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- Formal Bessel J₀ and the harmonic correction have exactly
the Frobenius initial coefficients; in particular no singular
logarithm is hidden in the formal correction. -/
@[simp] theorem besselFormalJ0_constantCoeff :
    PowerSeries.constantCoeff besselFormalJ0 = 1 := by
  simp [besselFormalJ0, PowerSeries.constantCoeff_mk]

@[simp] theorem besselFormalH0_constantCoeff :
    PowerSeries.constantCoeff besselFormalH0 = 0 := by
  simp [besselFormalH0, PowerSeries.constantCoeff_mk, harmonic_zero]

/-- Exact **unconditional formal** Wronskian identity for
the factorial and harmonic coefficients. No Wronskian
hypothesis and no imported special-function identity. -/
theorem besselFormalJ0H0_wronskian :
    FrobeniusWronskian.invariant besselFormalJ0 besselFormalH0 = 1 := by
  apply FrobeniusWronskian.invariant_eq_one
  · simpa only [Derivation.leibniz,
      PowerSeries.derivative_X, smul_eq_mul, mul_one, one_mul, add_comm] using
        besselFormalJ0_frobenius
  · simpa only [Derivation.leibniz,
      PowerSeries.derivative_X, smul_eq_mul, mul_one, one_mul, add_comm] using
        besselFormalH0_frobenius
  · exact besselFormalJ0_constantCoeff

end

end BesselFormal

/-!
# Formal Y₁ coefficients and the exact normalized harmonic Wronskian

The order-one correction of the concrete DLMF Y₁ series
is represented by the formal power series

  C(x) = Σ (Hₙ + Hₙ₊₁) xⁿ / (n!(n+1)!).

The harmonic recurrence gives a formal derivative relation

  x C = 2x B' - (A-1),

where A(x)=Σ xⁿ/(n!)² and B(x)=Σ Hₙxⁿ/(n!)²
are the concrete formal series defined in the preceding J₀/Y₀ coefficient section.

Inserting this relation into the proved Frobenius invariant
A²+2x(A'B-AB')=1 yields

  A+2x A'B-x A C=1.

After analytic evaluation at x=-z²/4, this yields the corresponding
complex Bessel J/Y harmonic-series identity. The formal identity is unconditional;
passing to analytic sums needs a separate justified
evaluation/Cauchy product theorem, not an assertion. This module contains
only generic formal Bessel series algebra, with no transport assumptions.
-/

namespace BesselFormal

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
  field_simp [hn, hf]; ring

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
    calc
      _ = 2 * ((n + 1 : ℕ) : ℂ) *
            PowerSeries.coeff (n + 1) besselFormalH0 -
          PowerSeries.coeff (n + 1) besselFormalJ0 := besselFormalH1_coeff n
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_one]
        ring

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
  unfold FrobeniusWronskian.invariant at hW
  linear_combination hW - besselFormalJ0 * hC

end

end BesselFormal
