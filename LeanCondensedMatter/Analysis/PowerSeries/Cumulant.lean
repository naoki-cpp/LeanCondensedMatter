import LeanCondensedMatter.Combinatorics.Cumulant.Inversion
import LeanCondensedMatter.Combinatorics.SetPartition.DistinguishedBlock
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Log

set_option linter.style.header false

/-!
# Formal-log coefficients and finite-set cumulants

This file identifies the factorial-normalized coefficients of the formal logarithm of a normalized
power series with finite-set cumulants.  The set-partition recursion used by the proof lives in the
pure combinatorics layer.
-/

open scoped BigOperators

namespace Combinatorics

open PowerSeries

/-- The exponential-generating-function normalization of a power-series coefficient. -/
noncomputable def powerSeriesMomentCoeff (Z : PowerSeries ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ) * PowerSeries.coeff n Z

/-- The exponential-generating-function normalization of a formal-log coefficient. -/
noncomputable def powerSeriesCumulantCoeff (Z : PowerSeries ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ) * PowerSeries.coeff n (PowerSeries.logOf Z)

private theorem derivative_log_mul_one_add_X :
    d⁄dX ℂ (PowerSeries.log ℂ) * (1 + PowerSeries.X) = 1 := by
  rw [PowerSeries.deriv_log, mul_add, mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_mk, pow_succ]

private theorem derivative_logOf_mul {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    d⁄dX ℂ (PowerSeries.logOf Z) * Z = d⁄dX ℂ Z := by
  have hsub : PowerSeries.HasSubst (Z - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hZ])
  have hgeom := congrArg (fun f : PowerSeries ℂ => f.subst (Z - 1))
    derivative_log_mul_one_add_X
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

/-- The factorial-normalized moment and formal-log coefficients satisfy the triangular
moment-cumulant recurrence. -/
theorem powerSeriesMomentCoeff_succ_recurrence {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) (n : ℕ) :
    powerSeriesMomentCoeff Z (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * powerSeriesCumulantCoeff Z (k + 1) *
          powerSeriesMomentCoeff Z (n - k) := by
  have hcoeff := congrArg (PowerSeries.coeff n) (derivative_logOf_mul hZ)
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

private theorem momentFromCumulant_powerSeriesCumulantCoeff
    {α : Type*} [DecidableEq α] {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) (s : Finset α) :
    Finpartition.momentFromCumulant
        (fun T : Finset α => powerSeriesCumulantCoeff Z T.card) s =
      powerSeriesMomentCoeff Z s.card := by
  classical
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hs : s = ∅
  · subst s
    letI : Unique (Finpartition (∅ : Finset α)) :=
      inferInstanceAs (Unique (Finpartition (⊥ : Finset α)))
    rw [Finpartition.momentFromCumulant, Fintype.sum_unique]
    have hparts : (default : Finpartition (∅ : Finset α)).parts = ∅ := by simp
    simp [Finpartition.partitionProduct, powerSeriesMomentCoeff, hZ, hparts]
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    rw [Finpartition.momentFromCumulant_eq_sum_blockContaining _ ha]
    have hsmall : ∀ B : Finpartition.BlockContaining s a,
        Finpartition.momentFromCumulant
            (fun T : Finset α => powerSeriesCumulantCoeff Z T.card) (s \ B.1) =
          powerSeriesMomentCoeff Z (s \ B.1).card := by
      intro B
      exact ih (s \ B.1) (Finset.sdiff_ssubset B.2.1 ⟨a, B.2.2⟩)
    simp_rw [hsmall]
    let n := s.card - 1
    have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
    have hcard : s.card = n + 1 := by
      dsimp [n]
      omega
    calc
      (∑ B : Finpartition.BlockContaining s a,
          powerSeriesCumulantCoeff Z B.1.card *
            powerSeriesMomentCoeff Z (s \ B.1).card) =
          ∑ B : Finpartition.BlockContaining s a,
            powerSeriesCumulantCoeff Z B.1.card *
              powerSeriesMomentCoeff Z (s.card - B.1.card) := by
        apply Fintype.sum_congr
        intro B
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr B.2.1]
      _ = ∑ k ∈ Finset.range s.card,
          (Nat.choose (s.card - 1) k : ℂ) *
            (powerSeriesCumulantCoeff Z (k + 1) *
              powerSeriesMomentCoeff Z (s.card - (k + 1))) := by
        exact Finpartition.sum_blockContaining_card s a ha
          (fun j => powerSeriesCumulantCoeff Z j *
            powerSeriesMomentCoeff Z (s.card - j))
      _ = powerSeriesMomentCoeff Z s.card := by
        rw [hcard]
        simpa [Nat.succ_eq_add_one, mul_assoc] using
          (powerSeriesMomentCoeff_succ_recurrence hZ n).symm

/-- Factorial-normalized coefficients of `logOf Z` are the finite-set cumulants of the
factorial-normalized coefficients of `Z`. -/
theorem factorial_mul_coeff_logOf_eq_cumulantFromMoment
    {Z : PowerSeries ℂ} (hZ : PowerSeries.constantCoeff Z = 1)
    {α : Type*} [DecidableEq α] {s : Finset α} (hs : s ≠ ∅) :
    (s.card.factorial : ℂ) * PowerSeries.coeff s.card (PowerSeries.logOf Z) =
      Finpartition.cumulantFromMoment
        (fun T : Finset α =>
          (T.card.factorial : ℂ) * PowerSeries.coeff T.card Z) s := by
  let κ : Finset α → ℂ := fun T => powerSeriesCumulantCoeff Z T.card
  have hm :
      (fun T : Finset α => powerSeriesMomentCoeff Z T.card) =
        Finpartition.momentFromCumulant κ := by
    funext T
    exact (momentFromCumulant_powerSeriesCumulantCoeff hZ T).symm
  change powerSeriesCumulantCoeff Z s.card = _
  change _ = Finpartition.cumulantFromMoment
    (fun T : Finset α => powerSeriesMomentCoeff Z T.card) s
  rw [hm]
  exact (Finpartition.cumulantFromMoment_momentFromCumulant κ hs).symm

/-- Cardinality-indexed form of the formal-log/finite-set-cumulant bridge. -/
theorem factorial_mul_coeff_logOf_eq_cumulantFromMoment_fin
    {Z : PowerSeries ℂ} (hZ : PowerSeries.constantCoeff Z = 1)
    (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) * PowerSeries.coeff n (PowerSeries.logOf Z) =
      Finpartition.cumulantFromMoment
        (fun S : Finset (Fin n) =>
          (S.card.factorial : ℂ) * PowerSeries.coeff S.card Z)
        Finset.univ := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have huniv : (Finset.univ : Finset (Fin n)) ≠ ∅ := by
    intro h
    have hx : (⟨0, hnpos⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_univ _
    rw [h] at hx
    simpa using hx
  simpa using
    (factorial_mul_coeff_logOf_eq_cumulantFromMoment hZ
      (s := (Finset.univ : Finset (Fin n))) huniv)

end Combinatorics
