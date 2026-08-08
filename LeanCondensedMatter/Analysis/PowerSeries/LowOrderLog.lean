import LeanCondensedMatter.Analysis.PowerSeries.Cumulant

set_option linter.style.header false

/-!
# Low-order coefficients of a normalized formal logarithm

This file exposes the first three factorial-normalized coefficients of `PowerSeries.logOf` in terms
of the coefficients of a power series with constant coefficient one.  The formulas are the first
three moment-cumulant identities and provide small, readable regression lemmas for applications.
-/

open scoped BigOperators

namespace Combinatorics

open PowerSeries

private theorem powerSeriesMomentCoeff_zero_eq_one {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    powerSeriesMomentCoeff Z 0 = 1 := by
  simp [powerSeriesMomentCoeff, PowerSeries.coeff_zero_eq_constantCoeff, hZ]

/-- The first cumulant coefficient equals the first moment coefficient. -/
theorem powerSeriesCumulantCoeff_one_eq {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    powerSeriesCumulantCoeff Z 1 = powerSeriesMomentCoeff Z 1 := by
  have hrec := powerSeriesMomentCoeff_succ_recurrence hZ 0
  norm_num [Finset.sum_range_succ, powerSeriesMomentCoeff_zero_eq_one hZ] at hrec
  simpa using hrec.symm

/-- The second cumulant coefficient subtracts the disconnected product of two first moments. -/
theorem powerSeriesCumulantCoeff_two_eq {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    powerSeriesCumulantCoeff Z 2 =
      powerSeriesMomentCoeff Z 2 - powerSeriesMomentCoeff Z 1 ^ 2 := by
  have hrec := powerSeriesMomentCoeff_succ_recurrence hZ 1
  norm_num [Finset.sum_range_succ, powerSeriesMomentCoeff_zero_eq_one hZ] at hrec
  rw [powerSeriesCumulantCoeff_one_eq hZ] at hrec
  ring_nf at hrec ⊢
  linear_combination -hrec

/-- The third cumulant coefficient removes all one-plus-two and three-singleton decompositions. -/
theorem powerSeriesCumulantCoeff_three_eq {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    powerSeriesCumulantCoeff Z 3 =
      powerSeriesMomentCoeff Z 3 -
        3 * powerSeriesMomentCoeff Z 1 * powerSeriesMomentCoeff Z 2 +
          2 * powerSeriesMomentCoeff Z 1 ^ 3 := by
  have hrec := powerSeriesMomentCoeff_succ_recurrence hZ 2
  norm_num [Finset.sum_range_succ, powerSeriesMomentCoeff_zero_eq_one hZ] at hrec
  rw [powerSeriesCumulantCoeff_one_eq hZ, powerSeriesCumulantCoeff_two_eq hZ] at hrec
  ring_nf at hrec ⊢
  linear_combination -hrec

/-- First factorial-normalized coefficient of `logOf Z`. -/
theorem factorial_mul_coeff_logOf_one_eq {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    ((1 : ℕ).factorial : ℂ) * PowerSeries.coeff 1 (PowerSeries.logOf Z) =
      PowerSeries.coeff 1 Z := by
  simpa [powerSeriesCumulantCoeff, powerSeriesMomentCoeff] using
    powerSeriesCumulantCoeff_one_eq hZ

/-- Second factorial-normalized coefficient of `logOf Z`. -/
theorem factorial_mul_coeff_logOf_two_eq {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    ((2 : ℕ).factorial : ℂ) * PowerSeries.coeff 2 (PowerSeries.logOf Z) =
      2 * PowerSeries.coeff 2 Z - PowerSeries.coeff 1 Z ^ 2 := by
  have h := powerSeriesCumulantCoeff_two_eq hZ
  norm_num [powerSeriesCumulantCoeff, powerSeriesMomentCoeff, Nat.factorial] at h ⊢
  exact h

/-- Third factorial-normalized coefficient of `logOf Z`. -/
theorem factorial_mul_coeff_logOf_three_eq {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    ((3 : ℕ).factorial : ℂ) * PowerSeries.coeff 3 (PowerSeries.logOf Z) =
      6 * PowerSeries.coeff 3 Z -
        6 * PowerSeries.coeff 1 Z * PowerSeries.coeff 2 Z +
          2 * PowerSeries.coeff 1 Z ^ 3 := by
  have h := powerSeriesCumulantCoeff_three_eq hZ
  norm_num [powerSeriesCumulantCoeff, powerSeriesMomentCoeff, Nat.factorial] at h ⊢
  ring_nf at h ⊢
  exact h

end Combinatorics
