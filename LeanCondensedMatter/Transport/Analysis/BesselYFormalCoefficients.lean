import LeanCondensedMatter.Transport.Analysis.BesselYFormalWronskian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# Concrete Frobenius coefficients for the J₀ / Y₀ harmonic correction

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

This file deliberately works in `ℂ⟦X⟧`; identifying
formal evaluation with the convergent analytic
`Complex.besselJ 0` and the concrete harmonic `tsum`
is the remaining separate analytic bridge.
-/

namespace QuantumTheory.Transport

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
  field_simp [hn, hf] <;> ring

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
  field_simp [hn, hf] <;> ring

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
          PowerSeries.coeff (n + 1) besselFormalJ0 := by ring
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
        PowerSeries.coeff (n + 1) besselFormalH0 := by ring
    _ = PowerSeries.coeff n besselFormalH0 +
        ((n + 1 : ℕ) : ℂ) *
          PowerSeries.coeff (n + 1) besselFormalJ0 := h
    _ = PowerSeries.coeff n
        (besselFormalH0 + PowerSeries.derivative besselFormalJ0) := by
      simp only [map_add, PowerSeries.coeff_derivative]
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
    besselFormalWronskianInvariant besselFormalJ0 besselFormalH0 = 1 := by
  apply besselFormalWronskianInvariant_eq_one
  · simpa only [Derivation.leibniz,
      PowerSeries.derivative_X, mul_one, one_mul, add_comm] using
        besselFormalJ0_frobenius
  · simpa only [Derivation.leibniz,
      PowerSeries.derivative_X, mul_one, one_mul, add_comm] using
        besselFormalH0_frobenius
  · exact besselFormalJ0_constantCoeff
  · exact besselFormalH0_constantCoeff

end

end QuantumTheory.Transport
