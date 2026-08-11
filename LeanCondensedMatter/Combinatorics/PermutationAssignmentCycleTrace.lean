import LeanCondensedMatter.Combinatorics.PermutationAssignmentCycleKernel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Trace

set_option linter.style.header false

/-!
# Assignment-summed cycle kernels and matrix traces

This file supplies the matrix-aware part of W3. Abstract cycle labels are separated from physical
matrix indices: an assignment `x : Fin m → ι` may repeat physical indices. The first step is to
show that the assignment-summed kernel depends only on the conjugacy class of the label cycle.
-/

namespace Combinatorics

open Finset

variable {ι R : Type*} [Fintype ι]

private noncomputable def cycleAssignmentKernelSum [CommSemiring R]
    (K : ι → ι → R) {m : ℕ} (σ : Equiv.Perm (Fin m)) : R :=
  ∑ x : Fin m → ι, ∏ a : Fin m, K (x a) (x (σ a))

private def assignmentRelabel {m : ℕ} (e : Equiv.Perm (Fin m)) :
    (Fin m → ι) ≃ (Fin m → ι) where
  toFun x := x ∘ e
  invFun x := x ∘ e.symm
  left_inv x := by
    funext a
    simp [Function.comp_def]
  right_inv x := by
    funext a
    simp [Function.comp_def]

omit [Fintype ι] in
private theorem cycleKernelWeight_conj [CommSemiring R] {m : ℕ}
    (K : ι → ι → R) (e σ : Equiv.Perm (Fin m)) (x : Fin m → ι) :
    (∏ a : Fin m, K (x a) (x ((e * σ * e⁻¹) a))) =
      ∏ a : Fin m, K ((x ∘ e) a) ((x ∘ e) (σ a)) := by
  classical
  calc
    (∏ a : Fin m, K (x a) (x ((e * σ * e⁻¹) a))) =
        ∏ a : Fin m, K (x (e a)) (x ((e * σ * e⁻¹) (e a))) := by
      exact (Equiv.prod_comp e (fun a => K (x a) (x ((e * σ * e⁻¹) a)))).symm
    _ = ∏ a : Fin m, K ((x ∘ e) a) ((x ∘ e) (σ a)) := by
      apply Finset.prod_congr rfl
      intro a _
      simp [Equiv.Perm.mul_apply]

private theorem cycleAssignmentKernelSum_conj [CommSemiring R] {m : ℕ}
    (K : ι → ι → R) (e σ : Equiv.Perm (Fin m)) :
    cycleAssignmentKernelSum K (e * σ * e⁻¹) = cycleAssignmentKernelSum K σ := by
  classical
  rw [cycleAssignmentKernelSum, cycleAssignmentKernelSum]
  calc
    (∑ x : Fin m → ι, ∏ a : Fin m, K (x a) (x ((e * σ * e⁻¹) a))) =
        ∑ x : Fin m → ι,
          ∏ a : Fin m, K ((assignmentRelabel e x) a) ((assignmentRelabel e x) (σ a)) := by
      apply Finset.sum_congr rfl
      intro x _
      simpa [assignmentRelabel] using cycleKernelWeight_conj K e σ x
    _ = ∑ x : Fin m → ι, ∏ a : Fin m, K (x a) (x (σ a)) := by
      exact Equiv.sum_comp (assignmentRelabel (ι := ι) e)
        (fun x => ∏ a : Fin m, K (x a) (x (σ a)))

private noncomputable def pathKernelWeight [CommSemiring R]
    (K : ι → ι → R) (a : ι) {n : ℕ} (v : Fin n → ι) (b : ι) : R :=
  ∏ i : Fin (n + 1),
    K ((Fin.cons a v : Fin (n + 1) → ι) i) ((Fin.snoc v b : Fin (n + 1) → ι) i)

private noncomputable def pathKernelSum [CommSemiring R]
    (K : ι → ι → R) (n : ℕ) (a b : ι) : R :=
  ∑ v : Fin n → ι, pathKernelWeight K a v b

omit [Fintype ι] in
private theorem pathKernelWeight_cons [CommSemiring R]
    (K : ι → ι → R) (a c b : ι) {n : ℕ} (v : Fin n → ι) :
    pathKernelWeight K a (Fin.cons c v) b = K a c * pathKernelWeight K c v b := by
  classical
  rw [pathKernelWeight, ← Fin.cons_snoc_eq_snoc_cons c v b, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rfl

private theorem pathKernelSum_succ [CommSemiring R]
    (K : ι → ι → R) (n : ℕ) (a b : ι) :
    pathKernelSum K (n + 1) a b = ∑ c : ι, K a c * pathKernelSum K n c b := by
  classical
  rw [pathKernelSum]
  calc
    (∑ v : Fin (n + 1) → ι, pathKernelWeight K a v b) =
        ∑ p : ι × (Fin n → ι), pathKernelWeight K a (Fin.cons p.1 p.2) b := by
      exact (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => ι))
        (fun v => pathKernelWeight K a v b)).symm
    _ = ∑ p : ι × (Fin n → ι), K a p.1 * pathKernelWeight K p.1 p.2 b := by
      apply Finset.sum_congr rfl
      intro p _
      exact pathKernelWeight_cons K a p.1 b p.2
    _ = ∑ c : ι, ∑ v : Fin n → ι, K a c * pathKernelWeight K c v b := by
      rw [Fintype.sum_prod_type]
    _ = ∑ c : ι, K a c * pathKernelSum K n c b := by
      apply Finset.sum_congr rfl
      intro c _
      rw [pathKernelSum, Finset.mul_sum]

private theorem pathKernelSum_eq_pow [CommSemiring R] [DecidableEq ι]
    (K : Matrix ι ι R) (n : ℕ) (a b : ι) :
    pathKernelSum K n a b = (K ^ (n + 1)) a b := by
  induction n generalizing a b with
  | zero =>
      simp [pathKernelSum, pathKernelWeight, Fin.snoc_zero]
  | succ n ih =>
      rw [pathKernelSum_succ]
      simp_rw [ih]
      change (K * K ^ (n + 1)) a b = (K ^ ((n + 1) + 1)) a b
      exact congrArg (fun M : Matrix ι ι R => M a b) (pow_succ' K (n + 1)).symm

omit [Fintype ι] in
private theorem cycleKernelWeight_finRotate [CommSemiring R] {n : ℕ}
    (K : ι → ι → R) (x : Fin (n + 1) → ι) :
    (∏ i : Fin (n + 1), K (x i) (x (finRotate (n + 1) i))) =
      pathKernelWeight K (x 0) (Fin.tail x) (x 0) := by
  classical
  have hcons : Fin.cons (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
  have hsnoc : Fin.snoc (Fin.tail x) (x 0) = fun i => x (finRotate (n + 1) i) := by
    rw [Fin.snoc_eq_cons_rotate, hcons]
  rw [pathKernelWeight, hcons, hsnoc]

private theorem cycleAssignmentKernelSum_finRotate_eq_trace [CommSemiring R] [DecidableEq ι]
    (K : Matrix ι ι R) (n : ℕ) :
    cycleAssignmentKernelSum K (finRotate (n + 1)) = Matrix.trace (K ^ (n + 1)) := by
  classical
  rw [cycleAssignmentKernelSum]
  simp_rw [cycleKernelWeight_finRotate]
  calc
    (∑ x : Fin (n + 1) → ι, pathKernelWeight K (x 0) (Fin.tail x) (x 0)) =
        ∑ p : ι × (Fin n → ι),
          pathKernelWeight K
            (((Fin.consEquiv (fun _ : Fin (n + 1) => ι)) p) 0)
            (Fin.tail ((Fin.consEquiv (fun _ : Fin (n + 1) => ι)) p))
            (((Fin.consEquiv (fun _ : Fin (n + 1) => ι)) p) 0) := by
      exact (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => ι))
        (fun x => pathKernelWeight K (x 0) (Fin.tail x) (x 0))).symm
    _ = ∑ p : ι × (Fin n → ι), pathKernelWeight K p.1 p.2 p.1 := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [Fin.consEquiv, Fin.cons_zero, Fin.tail_cons]
    _ = ∑ a : ι, pathKernelSum K n a a := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = Matrix.trace (K ^ (n + 1)) := by
      simp_rw [pathKernelSum_eq_pow]
      rfl

/-- Finite enumeration of full label cycles used in the W3 trace reduction. -/
noncomputable local instance assignmentTraceFullCycleFintype {m : ℕ} :
    Fintype {σ : Equiv.Perm (Fin m) // σ.IsCycleOn (Set.univ : Set (Fin m))} :=
  Fintype.ofFinite _

private theorem fullCycle_isCycle_add_two {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (hσ : σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))) : σ.IsCycle := by
  rw [Equiv.Perm.isCycle_iff_exists_isCycleOn]
  refine ⟨Set.univ, ?_, hσ, ?_⟩
  · refine ⟨0, by simp, 1, by simp, ?_⟩
    omega
  · simp

private theorem fullCycle_support_eq_univ_add_two {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (hσ : σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))) :
    σ.support = (Finset.univ : Finset (Fin (n + 2))) := by
  ext a
  simp only [Finset.mem_univ, iff_true]
  exact Equiv.Perm.mem_support.mpr (hσ.apply_ne (by
    refine ⟨0, by simp, 1, by simp, ?_⟩
    omega) (by simp))

private theorem fullCycle_isConj_finRotate_add_two {n : ℕ}
    (σ : {σ : Equiv.Perm (Fin (n + 2)) // σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))}) :
    IsConj σ.1 (finRotate (n + 2)) := by
  have hσcycle := fullCycle_isCycle_add_two σ.1 σ.2
  have hrot : (finRotate (n + 2)).IsCycle :=
    Equiv.Perm.isCycle_finRotate_of_le (by omega)
  apply hσcycle.isConj hrot
  rw [fullCycle_support_eq_univ_add_two σ.1 σ.2,
    Equiv.Perm.support_finRotate_of_le (by omega)]

private theorem cycleAssignmentKernelSum_fullCycle_add_two [CommSemiring R] [DecidableEq ι]
    (K : Matrix ι ι R) {n : ℕ}
    (σ : {σ : Equiv.Perm (Fin (n + 2)) // σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))}) :
    cycleAssignmentKernelSum K σ.1 = Matrix.trace (K ^ (n + 2)) := by
  obtain ⟨e, he⟩ := (_root_.isConj_iff).1 (fullCycle_isConj_finRotate_add_two σ)
  calc
    cycleAssignmentKernelSum K σ.1 =
        cycleAssignmentKernelSum K (e * σ.1 * e⁻¹) :=
      (cycleAssignmentKernelSum_conj K e σ.1).symm
    _ = cycleAssignmentKernelSum K (finRotate (n + 2)) := by rw [he]
    _ = Matrix.trace (K ^ (n + 2)) := by
      simpa only [Nat.add_assoc] using cycleAssignmentKernelSum_finRotate_eq_trace K (n + 1)

private theorem isCycleOn_univ_iff_cycleType_add_two {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) :
    σ.IsCycleOn (Set.univ : Set (Fin (n + 2))) ↔ σ.cycleType = {n + 2} := by
  constructor
  · intro hσ
    have hcycle := fullCycle_isCycle_add_two σ hσ
    rw [hcycle.cycleType, fullCycle_support_eq_univ_add_two σ hσ]
    simp
  · intro htype
    have hcycle : σ.IsCycle := by
      apply (Equiv.Perm.card_cycleType_eq_one).1
      simp [htype]
    have hsingleton : ({#σ.support} : Multiset ℕ) = {n + 2} := by
      calc
        ({#σ.support} : Multiset ℕ) = σ.cycleType := hcycle.cycleType.symm
        _ = {n + 2} := htype
    have hcard : #σ.support = n + 2 := by simpa using hsingleton
    have hsupp : σ.support = (Finset.univ : Finset (Fin (n + 2))) := by
      apply (Finset.card_eq_iff_eq_univ).1
      simpa using hcard
    have hset : {x : Fin (n + 2) | σ x ≠ x} = Set.univ := by
      ext x
      simp [← Equiv.Perm.mem_support, hsupp]
    rw [← hset]
    exact hcycle.isCycleOn

private noncomputable def fullCycleEquivCycleTypeAddTwo (n : ℕ) :
    {σ : Equiv.Perm (Fin (n + 2)) // σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))} ≃
      ↥({σ : Equiv.Perm (Fin (n + 2)) | σ.cycleType = {n + 2}} :
        Finset (Equiv.Perm (Fin (n + 2)))) where
  toFun σ := ⟨σ.1, by simpa using (isCycleOn_univ_iff_cycleType_add_two σ.1).1 σ.2⟩
  invFun σ := ⟨σ.1, (isCycleOn_univ_iff_cycleType_add_two σ.1).2 (by simpa using σ.2)⟩
  left_inv σ := Subtype.ext rfl
  right_inv σ := Subtype.ext rfl

private theorem fullCycle_card_add_two (n : ℕ) :
    Fintype.card
      {σ : Equiv.Perm (Fin (n + 2)) // σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))} =
      (n + 1)! := by
  classical
  calc
    Fintype.card
        {σ : Equiv.Perm (Fin (n + 2)) // σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))} =
      Fintype.card
        ↥({σ : Equiv.Perm (Fin (n + 2)) | σ.cycleType = {n + 2}} :
          Finset (Equiv.Perm (Fin (n + 2)))) :=
      Fintype.card_congr (fullCycleEquivCycleTypeAddTwo n)
    _ = #({σ : Equiv.Perm (Fin (n + 2)) | σ.cycleType = {n + 2}} :
        Finset (Equiv.Perm (Fin (n + 2)))) := by simp
    _ = (n + 1)! := by
      simpa using
        (Equiv.Perm.card_of_cycleType_singleton (α := Fin (n + 2)) (n := n + 2)
          (by omega) (by simp))

private theorem cycleAssignmentKernelSum_fullCycle_one [CommSemiring R] [DecidableEq ι]
    (K : Matrix ι ι R)
    (σ : {σ : Equiv.Perm (Fin 1) // σ.IsCycleOn (Set.univ : Set (Fin 1))}) :
    cycleAssignmentKernelSum K σ.1 = Matrix.trace (K ^ 1) := by
  have hσ : σ.1 = finRotate 1 := Subsingleton.elim _ _
  rw [hσ]
  simpa using cycleAssignmentKernelSum_finRotate_eq_trace K 0

private theorem fullCycle_card_one :
    Fintype.card {σ : Equiv.Perm (Fin 1) // σ.IsCycleOn (Set.univ : Set (Fin 1))} = 1 := by
  classical
  let defaultCycle :
      {σ : Equiv.Perm (Fin 1) // σ.IsCycleOn (Set.univ : Set (Fin 1))} :=
    ⟨1, by simp⟩
  letI : Unique {σ : Equiv.Perm (Fin 1) // σ.IsCycleOn (Set.univ : Set (Fin 1))} :=
    { default := defaultCycle
      uniq := fun σ => Subtype.ext (Subsingleton.elim _ _) }
  exact Fintype.card_unique

private theorem assignmentSingleCycleKernelSum_eq_sum_cycleAssignmentKernelSum [CommSemiring R]
    (K : ι → ι → R) (m : ℕ) :
    assignmentSingleCycleKernelSum K m =
      ∑ σ : {σ : Equiv.Perm (Fin m) // σ.IsCycleOn (Set.univ : Set (Fin m))},
        cycleAssignmentKernelSum K σ.1 := by
  classical
  rw [assignmentSingleCycleKernelSum]
  simp_rw [singleCycleKernelSum_univ_eq_sum_isCycleOn]
  rw [Fintype.sum_comm]
  rfl

/-- Assignment summation restores repeated physical indices and turns the full-cycle kernel into
`(m - 1)!` copies of the matrix trace. The empty label set is excluded because its connected
combinatorial term and `trace (K ^ 0)` have different meanings. -/
theorem assignmentSingleCycleKernelSum_eq_factorial_mul_trace [CommSemiring R] [DecidableEq ι]
    (K : Matrix ι ι R) (m : ℕ) (hm : 0 < m) :
    assignmentSingleCycleKernelSum K m =
      ((m - 1)! : R) * Matrix.trace (K ^ m) := by
  cases m with
  | zero => omega
  | succ m =>
      cases m with
      | zero =>
          rw [assignmentSingleCycleKernelSum_eq_sum_cycleAssignmentKernelSum]
          simp_rw [cycleAssignmentKernelSum_fullCycle_one]
          simp [fullCycle_card_one]
      | succ n =>
          rw [assignmentSingleCycleKernelSum_eq_sum_cycleAssignmentKernelSum]
          simp_rw [cycleAssignmentKernelSum_fullCycle_add_two]
          simp [fullCycle_card_add_two]

end Combinatorics
