import LeanCondensedMatter.Combinatorics.Cumulant.Moment
import LeanCondensedMatter.Combinatorics.SetPartition.Stirling
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

/-!
# Replica polynomials for finite-set connected expansions

A partition with `k` blocks admits an independent replica label on every block, producing the
factor `N^k`.  This file packages that block count into a polynomial in a formal replica variable
and extracts the coefficient linear in the replica count.

The construction is purely combinatorial.  In particular, it does not use partition-lattice
Möbius inversion or finite-set cumulant inversion.
-/

open scoped BigOperators

namespace Finpartition

variable {α R : Type*} [DecidableEq α] [CommSemiring R]

/-- The replica-count polynomial associated with finite-set block weights.

Each partition contributes its block-product weight in degree equal to its number of blocks. -/
noncomputable def replicaPolynomial (κ : Finset α → R) (S : Finset α) : Polynomial R :=
  ∑ π : Finpartition S,
    Polynomial.C (partitionProduct κ π) * Polynomial.X ^ π.parts.card

private theorem finpartition_eq_indiscrete_of_card_parts_eq_one
    {S : Finset α} (hS : S ≠ ∅) (π : Finpartition S) (hπ : π.parts.card = 1) :
    π = indiscrete hS := by
  obtain ⟨B, hparts⟩ := Finset.card_eq_one.mp hπ
  have hBS : B = S := by
    simpa [hparts] using π.sup_parts
  subst B
  apply Finpartition.ext
  simpa using hparts

/-- For nonempty support, the coefficient linear in the replica count is exactly the one-block
contribution. -/
theorem replicaPolynomial_coeff_one (κ : Finset α → R) {S : Finset α} (hS : S ≠ ∅) :
    (replicaPolynomial κ S).coeff 1 = κ S := by
  classical
  rw [replicaPolynomial, Polynomial.finsetSum_coeff]
  change (∑ π : Finpartition S,
    (Polynomial.C (partitionProduct κ π) *
      Polynomial.X ^ π.parts.card).coeff 1) = κ S
  rw [Fintype.sum_eq_single (Finpartition.indiscrete hS) (fun π hπ => by
    have hcard : 1 ≠ π.parts.card := by
      intro h
      exact hπ (finpartition_eq_indiscrete_of_card_parts_eq_one hS π h.symm)
    simp [hcard])]
  simp [partitionProduct]


/-- Evaluating the replica polynomial at a natural replica number is the sum over independent
replica labelings of the blocks of every partition. Each labeling carries the partition's block
weight. -/
theorem replicaPolynomial_eval_nat_eq_sum_labelings
    (κ : Finset α → R) (S : Finset α) (n : ℕ) :
    (replicaPolynomial κ S).eval (n : R) =
      ∑ π : Finpartition S, ∑ _ : π.parts → Fin n, partitionProduct κ π := by
  classical
  rw [replicaPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro π hπ
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  simp [Fintype.card_fin, nsmul_eq_mul, mul_comm]




private def fixedCardRefinementSigmaEquiv
    {S : Finset α} (k : ℕ) :
    (Σ σ : {σ : Finpartition S // σ.parts.card = k},
      {ρ : Finpartition S // ρ ≤ σ.1}) ≃
      Σ ρ : Finpartition S,
        {σ : {σ : Finpartition S // ρ ≤ σ} // σ.1.parts.card = k} where
  toFun x := ⟨x.2.1, ⟨⟨x.1.1, x.2.2⟩, x.1.2⟩⟩
  invFun x := ⟨⟨x.2.1.1, x.2.2⟩, ⟨x.1, x.2.1.2⟩⟩
  left_inv x := by
    rcases x with ⟨⟨σ, hσ⟩, ⟨ρ, hρ⟩⟩
    rfl
  right_inv x := by
    rcases x with ⟨ρ, ⟨⟨σ, hρ⟩, hσ⟩⟩
    rfl

/-- Summing products of moments over outer partitions with `k` blocks can be reindexed by the
underlying fine partition.  The multiplicity of a fine partition is the Stirling number counting
its `k`-block coarsenings. -/
theorem sum_partitionProduct_momentFromCumulant_partsCard_eq
    (κ : Finset α → R) (S : Finset α) (k : ℕ) :
    (∑ σ : {σ : Finpartition S // σ.parts.card = k},
        partitionProduct (momentFromCumulant κ) σ.1) =
      ∑ ρ : Finpartition S,
        (Nat.stirlingSecond ρ.parts.card k : R) * partitionProduct κ ρ := by
  classical
  have houter : ∀ σ : {σ : Finpartition S // σ.parts.card = k},
      partitionProduct (momentFromCumulant κ) σ.1 =
        ∑ ρ : {ρ : Finpartition S // ρ ≤ σ.1}, partitionProduct κ ρ.1 := by
    intro σ
    have hIic :
        (∑ ρ : {ρ : Finpartition S // ρ ≤ σ.1}, partitionProduct κ ρ.1) =
          ∑ ρ ∈ Finset.Iic σ.1, partitionProduct κ ρ := by
      rw [← Finset.sum_coe_sort (Finset.Iic σ.1) (partitionProduct κ)]
      refine Fintype.sum_equiv
        (Equiv.subtypeEquivRight (fun ρ => Finset.mem_Iic (a := σ.1).symm))
        (fun ρ : {ρ : Finpartition S // ρ ≤ σ.1} => partitionProduct κ ρ.1)
        (fun ρ : {ρ : Finpartition S // ρ ∈ Finset.Iic σ.1} =>
          partitionProduct κ ρ.1) fun x => ?_
      rw [Equiv.subtypeEquivRight_apply]
    rw [← sum_Iic_partitionProduct_eq κ σ.1, ← hIic]
  calc
    (∑ σ : {σ : Finpartition S // σ.parts.card = k},
        partitionProduct (momentFromCumulant κ) σ.1) =
        ∑ σ : {σ : Finpartition S // σ.parts.card = k},
          ∑ ρ : {ρ : Finpartition S // ρ ≤ σ.1}, partitionProduct κ ρ.1 := by
            apply Fintype.sum_congr
            intro σ
            exact houter σ
    _ = ∑ x :
        (Σ σ : {σ : Finpartition S // σ.parts.card = k},
          {ρ : Finpartition S // ρ ≤ σ.1}), partitionProduct κ x.2.1 := by
          rw [Fintype.sum_sigma]
    _ = ∑ x :
        (Σ ρ : Finpartition S,
          {σ : {σ : Finpartition S // ρ ≤ σ} // σ.1.parts.card = k}),
          partitionProduct κ x.1 := by
          refine Fintype.sum_equiv (fixedCardRefinementSigmaEquiv (S := S) k)
            (fun x => partitionProduct κ x.2.1)
            (fun x => partitionProduct κ x.1) ?_
          intro x
          rfl
    _ = ∑ ρ : Finpartition S,
        ∑ _ : {σ : {σ : Finpartition S // ρ ≤ σ} // σ.1.parts.card = k},
          partitionProduct κ ρ := by
          rw [Fintype.sum_sigma]
    _ = ∑ ρ : Finpartition S,
        (Nat.stirlingSecond ρ.parts.card k : R) * partitionProduct κ ρ := by
          apply Fintype.sum_congr
          intro ρ
          simp [card_coarsenings_parts_eq_stirlingSecond, nsmul_eq_mul]


section Ring

variable {F : Type*} [CommRing F]

private theorem descPochhammer_mul_X (k : ℕ) :
    descPochhammer F k * Polynomial.X =
      Polynomial.C (k : F) * descPochhammer F k + descPochhammer F (k + 1) := by
  rw [descPochhammer_succ_right, ← Polynomial.C_eq_natCast]
  ring

private theorem X_pow_eq_sum_stirlingSecond_descPochhammer (b : ℕ) :
    (Polynomial.X : Polynomial F) ^ b =
      ∑ k ∈ Finset.range (b + 1),
        Polynomial.C (Nat.stirlingSecond b k : F) * descPochhammer F k := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hshift :
          (∑ k ∈ Finset.range (b + 1),
              Polynomial.C (Nat.stirlingSecond b k : F) *
                (Polynomial.C (k : F) * descPochhammer F k)) =
            ∑ k ∈ Finset.range (b + 1),
              Polynomial.C (k + 1 : F) *
                (Polynomial.C (Nat.stirlingSecond b (k + 1) : F) *
                  descPochhammer F (k + 1)) := by
        rw [Finset.sum_range_succ'
            (fun k => Polynomial.C (Nat.stirlingSecond b k : F) *
              (Polynomial.C (k : F) * descPochhammer F k)) b,
          Finset.sum_range_succ
            (fun k => Polynomial.C (k + 1 : F) *
              (Polynomial.C (Nat.stirlingSecond b (k + 1) : F) *
                descPochhammer F (k + 1))) b,
          Nat.stirlingSecond_eq_zero_of_lt b.lt_add_one]
        simp [mul_assoc, mul_left_comm, mul_comm]
      rw [pow_succ, ih, Finset.sum_mul,
        Finset.sum_range_succ'
          (fun k => Polynomial.C (Nat.stirlingSecond (b + 1) k : F) *
            descPochhammer F k) (b + 1)]
      simp only [mul_assoc, descPochhammer_mul_X, mul_add, Finset.sum_add_distrib, hshift,
        Nat.stirlingSecond_succ_succ, Nat.cast_add, Nat.cast_mul, map_add, map_mul,
        Nat.stirlingSecond_succ_zero, Nat.cast_zero, map_zero, zero_mul, add_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- The replica polynomial in the descending-factorial basis.  The Stirling number of the second
kind converts the monomial replica factor for a partition into the falling-factorial basis used by
the fixed-order power-series replica polynomial. -/
theorem replicaPolynomial_eq_sum_stirlingSecond_descPochhammer
    {α : Type*} [DecidableEq α] (κ : Finset α → F) (S : Finset α) :
    replicaPolynomial κ S =
      ∑ π : Finpartition S, ∑ k ∈ Finset.range (π.parts.card + 1),
        Polynomial.C
            ((Nat.stirlingSecond π.parts.card k : F) * partitionProduct κ π) *
          descPochhammer F k := by
  classical
  rw [replicaPolynomial]
  apply Finset.sum_congr rfl
  intro π hπ
  rw [X_pow_eq_sum_stirlingSecond_descPochhammer]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [mul_assoc, mul_comm]

end Ring

end Finpartition
