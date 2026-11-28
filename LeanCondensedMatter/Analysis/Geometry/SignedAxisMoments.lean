import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Moments of a kernel on signed coordinate axes

A signed coordinate axis is indexed by an arbitrary finite set and a two-element sign.
The dot product takes only three values. Its weighted sums reduce to a constant background
and the two distinguished parallel and antiparallel directions.
-/

namespace FiniteAngularKernel

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The signed unit coordinate vector associated with an axis and a sign. -/
def signedAxisDirection (p : ι × Fin 2) (i : ι) : ℝ :=
  if p.1 = i then (if p.2 = 0 then 1 else -1) else 0

/-- Dot product between two signed coordinate vectors. -/
def signedAxisCosine (p q : ι × Fin 2) : ℝ :=
  ∑ i, signedAxisDirection p i * signedAxisDirection q i

theorem signedAxisCosine_eq (p q : ι × Fin 2) :
    signedAxisCosine p q = if p.1 = q.1 then
      (if p.2 = q.2 then 1 else -1) else 0 := by
  rcases p with ⟨a, s⟩
  rcases q with ⟨b, t⟩
  by_cases hab : a = b
  · subst b
    rw [signedAxisCosine]
    rw [Finset.sum_eq_single a]
    · fin_cases s <;> fin_cases t <;> simp [signedAxisDirection]
    · intro i _ hi
      simp [signedAxisDirection, Ne.symm hi]
    · simp
  · rw [signedAxisCosine, ite_eq_right hab]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : a = i
    · have hj : b ≠ i := fun h => hab (hi.trans h.symm)
      simp [signedAxisDirection, hi, hj]
    · simp [signedAxisDirection, hi]

theorem signedAxis_unit (p : ι × Fin 2) :
    ∑ i, signedAxisDirection p i ^ 2 = 1 := by
  simpa [signedAxisCosine, pow_two] using signedAxisCosine_eq p p

omit [Fintype ι] in
theorem signedAxisDirection_rev (p : ι × Fin 2) (i : ι) :
    signedAxisDirection (p.1, p.2.rev) i = -signedAxisDirection p i := by
  rcases p with ⟨a, s⟩
  fin_cases s <;> by_cases h : a = i <;>
    norm_num [signedAxisDirection, Fin.rev, h]

/-- Every weighted sum decomposes into the orthogonal-channel background and corrections
at the parallel and antiparallel vectors. -/
theorem signedAxis_sum_weighted (W : ℝ → ℝ) (p : ι × Fin 2) (f : ι × Fin 2 → ℝ) :
    (∑ q, W (signedAxisCosine p q) * f q) =
      W 0 * (∑ q, f q) + (W 1 - W 0) * f p +
        (W (-1) - W 0) * f (p.1, p.2.rev) := by
  have h (q : ι × Fin 2) :
      W (signedAxisCosine p q) * f q =
        W 0 * f q + (if q = p then (W 1 - W 0) * f q else 0) +
          (if q = (p.1, p.2.rev) then (W (-1) - W 0) * f q else 0) := by
    rcases p with ⟨a, s⟩
    rcases q with ⟨b, t⟩
    by_cases hab : a = b
    · subst b
      fin_cases s <;> fin_cases t <;>
        norm_num [signedAxisCosine_eq, Fin.rev] <;> ring
    · simp [signedAxisCosine_eq, hab, Ne.symm hab]
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

theorem signedAxis_sum_direction (i : ι) :
    ∑ q : ι × Fin 2, signedAxisDirection q i = 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro a _
  by_cases h : a = i <;> simp [Fin.sum_univ_two, signedAxisDirection, h]

theorem signedAxis_sum_direction_mul (i j : ι) :
    ∑ q : ι × Fin 2, signedAxisDirection q i * signedAxisDirection q j =
      if i = j then 2 else 0 := by
  rw [Fintype.sum_prod_type]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    calc
      _ = ∑ a : ι, if a = i then (2 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : a = i <;>
          norm_num [Fin.sum_univ_two, signedAxisDirection, h]
      _ = 2 := by simp
  · rw [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hi : a = i
    · subst a
      simp [signedAxisDirection, hij]
    · simp [signedAxisDirection, hi]

/-- The total gain rate in any finite dimension. -/
theorem signedAxis_total_moment (W : ℝ → ℝ) (p : ι × Fin 2) :
    ∑ q, W (signedAxisCosine p q) =
      W 1 + W (-1) + (2 * (Fintype.card ι : ℝ) - 2) * W 0 := by
  have h := signedAxis_sum_weighted W p (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h
  rw [h]
  ring

/-- First coordinate gain moment. -/
theorem signedAxis_first_moment (W : ℝ → ℝ) (p : ι × Fin 2) (i : ι) :
    ∑ q, W (signedAxisCosine p q) * signedAxisDirection q i =
      (W 1 - W (-1)) * signedAxisDirection p i := by
  rw [signedAxis_sum_weighted W p (fun q => signedAxisDirection q i),
    signedAxis_sum_direction, mul_zero, zero_add, signedAxisDirection_rev]
  ring

/-- Second coordinate gain moment, without any division by dimension. -/
theorem signedAxis_second_moment (W : ℝ → ℝ) (p : ι × Fin 2) (i j : ι) :
    ∑ q, W (signedAxisCosine p q) * (signedAxisDirection q i * signedAxisDirection q j) =
      2 * W 0 * (if i = j then 1 else 0) +
        (W 1 + W (-1) - 2 * W 0) * (signedAxisDirection p i * signedAxisDirection p j) := by
  rw [signedAxis_sum_weighted W p
    (fun q => signedAxisDirection q i * signedAxisDirection q j),
    signedAxis_sum_direction_mul, signedAxisDirection_rev, signedAxisDirection_rev]
  split_ifs <;> ring

end FiniteAngularKernel
