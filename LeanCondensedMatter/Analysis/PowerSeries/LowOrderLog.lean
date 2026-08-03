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

private theorem derivative_log_mul_one_add_X_lowOrder :
    d⁄dX ℂ (PowerSeries.log ℂ) * (1 + PowerSeries.X) = 1 := by
  rw [PowerSeries.deriv_log, mul_add, mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_mk, pow_succ]

private theorem derivative_logOf_mul_lowOrder {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    d⁄dX ℂ (PowerSeries.logOf Z) * Z = d⁄dX ℂ Z := by
  have hsub : PowerSeries.HasSubst (Z - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hZ])
  have hgeom := congrArg (fun f : PowerSeries ℂ => f.subst (Z - 1))
    derivative_log_mul_one_add_X_lowOrder
  have hone : (1 : PowerSeries ℂ).subst (Z - 1) = 1 := by
    rw [show (1 : PowerSeries ℂ) = PowerSeries.C 1 by rfl, PowerSeries.subst_C]
    rfl
  have hgeom' :
      (d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * Z = 1 := by
    rw [PowerSeries.subst_mul hsub, PowerSeries.subst_add hsub,
      PowerSeries.subst_X hsub, hone] at hgeom
    simpa using hgeom
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst ℂ hsub]
  have hderiv : d⁄dX ℂ (Z - 1) = d⁄dX ℂ Z := by simp
  rw [hderiv]
  calc
    ((d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * d⁄dX ℂ Z) * Z =
        ((d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * Z) * d⁄dX ℂ Z := by
          ring
    _ = d⁄dX ℂ Z := by rw [hgeom']; simp

private theorem powerSeriesMomentCoeff_succ_recurrence_lowOrder
    {Z : PowerSeries ℂ} (hZ : PowerSeries.constantCoeff Z = 1) (n : ℕ) :
    powerSeriesMomentCoeff Z (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * powerSeriesCumulantCoeff Z (k + 1) *
          powerSeriesMomentCoeff Z (n - k) := by
  have hcoeff := congrArg (PowerSeries.coeff n) (derivative_logOf_mul_lowOrder hZ)
  rw [PowerSeries.coeff_mul] at hcoeff
  simp_rw [PowerSeries.coeff_derivative] at hcoeff
  calc
    powerSeriesMomentCoeff Z (n + 1) =
        (n.factorial : ℂ) * (PowerSeries.coeff (n + 1) Z * (n + 1 : ℂ)) := by
          simp [powerSeriesMomentCoeff, Nat.factorial_succ]
          ring
    _ = (n.factorial : ℂ) *
        (∑ p ∈ Finset.antidiagonal n,
          PowerSeries.coeff (p.1 + 1) (PowerSeries.logOf Z) * (p.1 + 1 : ℂ) *
            PowerSeries.coeff p.2 Z) := by rw [hcoeff]
    _ = ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * powerSeriesCumulantCoeff Z (k + 1) *
          powerSeriesMomentCoeff Z (n - k) := by
      rw [Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hnat := Nat.choose_mul_factorial_mul_factorial hkn
      have hfac :
          (n.factorial : ℂ) * (k + 1 : ℂ) =
            (Nat.choose n k : ℂ) * ((k + 1).factorial : ℂ) *
              ((n - k).factorial : ℂ) := by
        norm_cast
        calc
          n.factorial * (k + 1) = (k + 1) * n.factorial := by ac_rfl
          _ = (k + 1) * (Nat.choose n k * k.factorial * (n - k).factorial) := by
            rw [hnat]
          _ = Nat.choose n k * (k + 1).factorial * (n - k).factorial := by
            rw [Nat.factorial_succ]
            ac_rfl
      simp only [powerSeriesMomentCoeff, powerSeriesCumulantCoeff]
      calc
        (n.factorial : ℂ) *
            (PowerSeries.coeff (k + 1) (PowerSeries.logOf Z) * (k + 1 : ℂ) *
              PowerSeries.coeff (n - k) Z) =
            ((n.factorial : ℂ) * (k + 1 : ℂ)) *
              PowerSeries.coeff (k + 1) (PowerSeries.logOf Z) *
                PowerSeries.coeff (n - k) Z := by ring
        _ = ((Nat.choose n k : ℂ) * ((k + 1).factorial : ℂ) *
              ((n - k).factorial : ℂ)) *
              PowerSeries.coeff (k + 1) (PowerSeries.logOf Z) *
                PowerSeries.coeff (n - k) Z := by rw [hfac]
        _ = (Nat.choose n k : ℂ) *
              (((k + 1).factorial : ℂ) *
                PowerSeries.coeff (k + 1) (PowerSeries.logOf Z)) *
              (((n - k).factorial : ℂ) * PowerSeries.coeff (n - k) Z) := by ring

private theorem powerSeriesMomentCoeff_zero_eq_one {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    powerSeriesMomentCoeff Z 0 = 1 := by
  simp [powerSeriesMomentCoeff, PowerSeries.coeff_zero_eq_constantCoeff, hZ]

/-- The first cumulant coefficient equals the first moment coefficient. -/
theorem powerSeriesCumulantCoeff_one_eq {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    powerSeriesCumulantCoeff Z 1 = powerSeriesMomentCoeff Z 1 := by
  have hrec := powerSeriesMomentCoeff_succ_recurrence_lowOrder hZ 0
  norm_num [Finset.sum_range_succ, powerSeriesMomentCoeff_zero_eq_one hZ] at hrec
  simpa using hrec.symm

/-- The second cumulant coefficient subtracts the disconnected product of two first moments. -/
theorem powerSeriesCumulantCoeff_two_eq {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    powerSeriesCumulantCoeff Z 2 =
      powerSeriesMomentCoeff Z 2 - powerSeriesMomentCoeff Z 1 ^ 2 := by
  have hrec := powerSeriesMomentCoeff_succ_recurrence_lowOrder hZ 1
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
  have hrec := powerSeriesMomentCoeff_succ_recurrence_lowOrder hZ 2
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
