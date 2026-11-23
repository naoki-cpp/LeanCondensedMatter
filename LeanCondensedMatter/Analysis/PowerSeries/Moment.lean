import LeanCondensedMatter.Analysis.PowerSeries.Normalization
import LeanCondensedMatter.Combinatorics.Cumulant.NormalizedCore
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Factorial-normalized power-series moments

This module packages factorial-normalized power-series coefficients as finite-set moment data.
It is deliberately independent of cumulant inversion so both replica and Möbius-inversion proof
tracks can share the same moment interface. The formal logarithm's factorial-normalized
cumulant coefficients and their triangular recurrence are also defined here, without requiring
set-partition inversion or analytic convergence.
-/

namespace Combinatorics

open PowerSeries

/-- The exponential-generating-function normalization of a power-series coefficient. -/
noncomputable def powerSeriesMomentCoeff
    {R : Type*} [Semiring R] (Z : PowerSeries R) (n : ℕ) : R :=
  (n.factorial : R) * PowerSeries.coeff n Z

/-- Factorial-normalized coefficients of a unit-constant power series, bundled as normalized
finite-set moment data. -/
noncomputable def powerSeriesMomentSetFunction
    {α R : Type*} [Semiring R] (Z : PowerSeries R)
    (hZ : PowerSeries.constantCoeff Z = 1) :
    NormalizedSetFunction α R where
  toFun := fun S => powerSeriesMomentCoeff Z S.card
  map_empty := by
    simp [powerSeriesMomentCoeff, PowerSeries.coeff_zero_eq_constantCoeff, hZ]

/-- Equality of the bundled power-series moment function with normalized finite-set moment data is
equivalent to equality of the factorial-normalized coefficients on every finite set. -/
theorem powerSeriesMomentSetFunction_eq_iff
    {α R : Type*} [Semiring R] (Z : PowerSeries R)
    (hZ : PowerSeries.constantCoeff Z = 1)
    (M : NormalizedSetFunction α R) :
    powerSeriesMomentSetFunction Z hZ = M ↔
      ∀ S : Finset α, powerSeriesMomentCoeff Z S.card = M S := by
  constructor
  · rintro rfl S
    rfl
  · intro h
    exact NormalizedSetFunction.ext h

end Combinatorics

/-! ## Formal-log cumulant coefficients and moment recurrence -/

open scoped BigOperators

namespace Combinatorics

open PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The exponential-generating-function normalization of a formal-log coefficient. -/
noncomputable def powerSeriesCumulantCoeff (Z : PowerSeries R) (n : ℕ) : R :=
  (n.factorial : R) * PowerSeries.coeff n (PowerSeries.logOf Z)

/-- The factorial-normalized moment and formal-log coefficients satisfy the triangular
moment-cumulant recurrence. -/
theorem powerSeriesMomentCoeff_succ_recurrence {Z : PowerSeries R}
    (hZ : PowerSeries.constantCoeff Z = 1) (n : ℕ) :
    powerSeriesMomentCoeff Z (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : R) * powerSeriesCumulantCoeff Z (k + 1) *
          powerSeriesMomentCoeff Z (n - k) := by
  have hcoeff := congrArg (PowerSeries.coeff n) (PowerSeries.derivative_logOf_mul hZ)
  rw [PowerSeries.coeff_mul] at hcoeff
  simp_rw [PowerSeries.coeff_derivative] at hcoeff
  calc
    powerSeriesMomentCoeff Z (n + 1) =
        (n.factorial : R) * (PowerSeries.coeff (n + 1) Z * (n + 1 : R)) := by
          simp [powerSeriesMomentCoeff, Nat.factorial_succ]
          ring
    _ = (n.factorial : R) *
        (∑ p ∈ Finset.antidiagonal n,
          PowerSeries.coeff (p.1 + 1) (PowerSeries.logOf Z) * (p.1 + 1 : R) *
            PowerSeries.coeff p.2 Z) := by rw [hcoeff]
    _ = ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : R) * powerSeriesCumulantCoeff Z (k + 1) *
          powerSeriesMomentCoeff Z (n - k) := by
      rw [Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hnat := Nat.choose_mul_factorial_mul_factorial hkn
      have hfacNat :
          n.factorial * (k + 1) =
            Nat.choose n k * (k + 1).factorial * (n - k).factorial := by
        calc
          n.factorial * (k + 1) = (k + 1) * n.factorial := by ac_rfl
          _ = (k + 1) * (Nat.choose n k * k.factorial * (n - k).factorial) := by
            rw [hnat]
          _ = Nat.choose n k * (k + 1).factorial * (n - k).factorial := by
            rw [Nat.factorial_succ]
            ac_rfl
      have hfac :
          (n.factorial : R) * (k + 1 : R) =
            (Nat.choose n k : R) * ((k + 1).factorial : R) *
              ((n - k).factorial : R) := by
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
          congrArg (fun m : ℕ => (m : R)) hfacNat
      simp only [powerSeriesMomentCoeff, powerSeriesCumulantCoeff]
      calc
        (n.factorial : R) *
            (PowerSeries.coeff (k + 1) (PowerSeries.logOf Z) * (k + 1 : R) *
              PowerSeries.coeff (n - k) Z) =
            ((n.factorial : R) * (k + 1 : R)) *
              PowerSeries.coeff (k + 1) (PowerSeries.logOf Z) *
                PowerSeries.coeff (n - k) Z := by ring
        _ = ((Nat.choose n k : R) * ((k + 1).factorial : R) *
              ((n - k).factorial : R)) *
              PowerSeries.coeff (k + 1) (PowerSeries.logOf Z) *
                PowerSeries.coeff (n - k) Z := by rw [hfac]
        _ = (Nat.choose n k : R) *
              (((k + 1).factorial : R) *
                PowerSeries.coeff (k + 1) (PowerSeries.logOf Z)) *
              (((n - k).factorial : R) * PowerSeries.coeff (n - k) Z) := by ring

end Combinatorics
