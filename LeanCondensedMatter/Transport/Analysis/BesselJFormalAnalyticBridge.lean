import LeanCondensedMatter.Transport.Analysis.BesselYFormalCoefficients
import LeanCondensedMatter.Transport.Analysis.PolarFourier

set_option linter.style.header false

/-!
# Analytic J₀/J₁ bridge for the formal factorial series

The formal series `besselFormalJ0` is the unique normalized factorial
coefficient series already used in the unconditional formal Wronskian proof.
We identify its coefficients, and the coefficients of its formal derivative,
with Mathlib's regularized hypergeometric coefficients of parameters 1 and 2.

This gives actual, everywhere-summable complex `tsum` formulas
for `Complex.besselJ 0 z` and `Complex.besselJ 1 z` at
`x = -(z/2)^2`, with no invented evaluation of `ℂ⟦X⟧` at non-nilpotent
arguments. Transporting products through these evaluations requires a
separate Cauchy-product theorem.
-/

namespace QuantumTheory.Transport

noncomputable section

/-- The formal J₀ factorial coefficient agrees with the *actual*
regularized hypergeometric coefficient for bottom parameter 1. -/
theorem besselFormalJ0_coeff_eq_regularizedHGFun (n : ℕ) :
    PowerSeries.coeff n besselFormalJ0 =
      Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} n := by
  have h := regularizedHGFunCoeff_zero_singleton_nat_add_one 0 n
  simpa [besselFormalJ0, pow_two] using h.symm

/-- The formal derivative of J₀ has exactly the bottom-parameter-2
hypergeometric coefficients. This is a coefficient-level statement,
not analytic differentiation of an infinite sum. -/
theorem besselFormalJ0_derivative_coeff_eq_regularizedHGFun (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative besselFormalJ0) =
      Complex.regularizedHGFunCoeff 0 {(2 : ℂ)} n := by
  have hcoeff :
      Complex.regularizedHGFunCoeff 0 {(2 : ℂ)} n =
        1 / ((Nat.factorial n : ℂ) * (Nat.factorial (n + 1) : ℂ)) := by
    simpa using (regularizedHGFunCoeff_zero_singleton_nat_add_one 1 n)
  rw [PowerSeries.coeff_derivative, hcoeff]
  simp only [besselFormalJ0, PowerSeries.coeff_mk]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.factorial_succ]
  push_cast
  field_simp [hn, hf]

/-- Formal J₀ coefficients have an everywhere convergent complex
power-series evaluation, by the known entire hypergeometric series. -/
theorem summable_besselFormalJ0_eval (z : ℂ) :
    Summable (fun n : ℕ =>
      PowerSeries.coeff n besselFormalJ0 * (-(z / 2) ^ 2) ^ n) := by
  have hs :
      Summable (fun n : ℕ =>
        Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} n * (-(z / 2) ^ 2) ^ n) := by
    simpa only [Complex.regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
        (Complex.regularizedHGFunSeries 0 {(1 : ℂ)}).summable (by simp)
  simpa only [besselFormalJ0_coeff_eq_regularizedHGFun] using hs

/-- Formal J₀ derivative coefficients also have an everywhere
convergent complex evaluation. -/
theorem summable_besselFormalJ0_derivative_eval (z : ℂ) :
    Summable (fun n : ℕ =>
      PowerSeries.coeff n (PowerSeries.derivative besselFormalJ0) *
        (-(z / 2) ^ 2) ^ n) := by
  have hs :
      Summable (fun n : ℕ =>
        Complex.regularizedHGFunCoeff 0 {(2 : ℂ)} n * (-(z / 2) ^ 2) ^ n) := by
    simpa only [Complex.regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
        (Complex.regularizedHGFunSeries 0 {(2 : ℂ)}).summable (by simp)
  simpa only [besselFormalJ0_derivative_coeff_eq_regularizedHGFun] using hs

/-- Mathlib's J₀ is the coefficientwise entire evaluation of the
concrete formal factorial power series. -/
theorem besselJZero_eq_formalTsum (z : ℂ) :
    Complex.besselJ 0 z =
      ∑' n : ℕ, PowerSeries.coeff n besselFormalJ0 *
        (-(z / 2) ^ 2) ^ n := by
  rw [polarFourierBesselJZero_eq_tsum]
  apply tsum_congr
  intro n
  rw [besselFormalJ0_coeff_eq_regularizedHGFun]

/-- The order-one J function in Mathlib, in its bottom-parameter-2
hypergeometric series representation. -/
theorem besselJOne_eq_regularizedHGTsum (z : ℂ) :
    Complex.besselJ 1 z =
      (z / 2) * (∑' n : ℕ,
        Complex.regularizedHGFunCoeff 0 {(2 : ℂ)} n *
          (-(z / 2) ^ 2) ^ n) := by
  calc
    Complex.besselJ 1 z =
        (z / 2) * Complex.regularizedHGFun 0 {(2 : ℂ)} (-(z / 2) ^ 2) := by
      simp only [Complex.besselJ_def, Complex.cpow_one]
      congr 1
      norm_num
    _ = (z / 2) * (∑' n : ℕ,
          Complex.regularizedHGFunCoeff 0 {(2 : ℂ)} n *
            (-(z / 2) ^ 2) ^ n) := by
      congr 1
      rw [Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
        ← FormalMultilinearSeries.ofScalarsSum,
        FormalMultilinearSeries.ofScalars_sum_eq]
      simp only [smul_eq_mul]

/-- Analytic J₁ is the complex evaluation of the *formal derivative*
of the normalized J₀ factorial series, multiplied by z/2. No analytic
derivative-of-sum exchange is postulated. -/
theorem besselJOne_eq_formalDerivativeTsum (z : ℂ) :
    Complex.besselJ 1 z =
      (z / 2) * (∑' n : ℕ,
        PowerSeries.coeff n (PowerSeries.derivative besselFormalJ0) *
          (-(z / 2) ^ 2) ^ n) := by
  rw [besselJOne_eq_regularizedHGTsum]
  congr 1
  apply tsum_congr
  intro n
  rw [besselFormalJ0_derivative_coeff_eq_regularizedHGFun]

end

end QuantumTheory.Transport
