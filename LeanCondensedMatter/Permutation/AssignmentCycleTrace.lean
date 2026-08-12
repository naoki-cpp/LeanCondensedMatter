import LeanCondensedMatter.Permutation.SingleCycleKernel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Trace

set_option linter.style.header false

/-!
# Assignment-summed cycle kernels and matrix traces

This file owns the finite bridge from fixed-label single-cycle combinatorics to matrix traces.
Abstract cycle labels are `Fin m`, while `x : Fin m → ι` assigns physical indices to those labels;
repetitions are deliberately allowed. Assignment/counting intermediates remain file-private, and the
public boundary is the direct assignment-summed connected-contribution / trace theorem.
-/

namespace Combinatorics

open Finset

variable {ι R : Type*} [Fintype ι]

private noncomputable def assignmentSingleCycleKernelSum [CommSemiring R]
    (K : ι → ι → R) (m : ℕ) : R :=
  ∑ x : Fin m → ι,
    singleCycleKernelSum (fun a b : Fin m => K (x a) (x b)) Finset.univ

private theorem sum_singleCycleContribution_assignments_eq_pow_mul_assignmentSingleCycleKernelSum
    [CommSemiring R] (ζ : R) (K : ι → ι → R) (m : ℕ) :
    (∑ x : Fin m → ι,
      singleCycleContribution ζ (fun a b : Fin m => K (x a) (x b)) Finset.univ) =
      ζ ^ (m - 1) * assignmentSingleCycleKernelSum K m := by
  classical
  simp_rw [singleCycleContribution_eq_pow_card_mul_singleCycleKernelSum]
  simp [assignmentSingleCycleKernelSum, Finset.mul_sum]

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
      have hp :
          (Fin.consEquiv (fun _ : Fin (n + 1) => ι)) p =
            (Fin.cons p.1 p.2 : Fin (n + 1) → ι) := rfl
      rw [hp, Fin.cons_zero, Fin.tail_cons]
    _ = ∑ a : ι, pathKernelSum K n a a := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = Matrix.trace (K ^ (n + 1)) := by
      simp_rw [pathKernelSum_eq_pow]
      rfl

noncomputable local instance assignmentTraceFullCycleFintype {m : ℕ} :
    Fintype {σ : Equiv.Perm (Fin m) // σ.IsCycleOn (Set.univ : Set (Fin m))} :=
  Fintype.ofFinite _

private theorem finAddTwo_univ_nontrivial (n : ℕ) :
    (Set.univ : Set (Fin (n + 2))).Nontrivial := by
  let a : Fin (n + 2) := ⟨0, by omega⟩
  let b : Fin (n + 2) := ⟨1, by omega⟩
  refine ⟨a, by simp, b, by simp, ?_⟩
  intro hab
  have hval := congrArg Fin.val hab
  simp [a, b] at hval

private theorem fullCycle_isCycle_add_two {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (hσ : σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))) : σ.IsCycle := by
  rw [Equiv.Perm.isCycle_iff_exists_isCycleOn]
  exact ⟨Set.univ, finAddTwo_univ_nontrivial n, hσ, by simp⟩

private theorem fullCycle_support_eq_univ_add_two {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (hσ : σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))) :
    σ.support = (Finset.univ : Finset (Fin (n + 2))) := by
  ext a
  simp only [Finset.mem_univ, iff_true]
  exact Equiv.Perm.mem_support.mpr
    (hσ.apply_ne (finAddTwo_univ_nontrivial n) (by simp))

private theorem fullCycle_isConj_finRotate_add_two {n : ℕ}
    (σ : {σ : Equiv.Perm (Fin (n + 2)) // σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))}) :
    IsConj σ.1 (finRotate (n + 2)) := by
  have hσcycle := fullCycle_isCycle_add_two σ.1 σ.2
  apply hσcycle.isConj isCycle_finRotate
  rw [fullCycle_support_eq_univ_add_two σ.1 σ.2, support_finRotate]

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
    have hsupp : σ.support = (Finset.univ : Finset (Fin (n + 2))) :=
      (Finset.card_eq_iff_eq_univ σ.support).1 (by simpa using hcard)
    have hset : {x : Fin (n + 2) | σ x ≠ x} = Set.univ := by
      ext x
      simp [← Equiv.Perm.mem_support, hsupp]
    rw [← hset]
    exact hcycle.isCycleOn

private noncomputable def fullCycleEquivCycleTypeAddTwo (n : ℕ) :
    {σ : Equiv.Perm (Fin (n + 2)) // σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))} ≃
      ↥({σ : Equiv.Perm (Fin (n + 2)) | σ.cycleType = {n + 2}} :
        Finset (Equiv.Perm (Fin (n + 2)))) where
  toFun σ := ⟨σ.1, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (isCycleOn_univ_iff_cycleType_add_two σ.1).1 σ.2⟩
  invFun σ := ⟨σ.1, (isCycleOn_univ_iff_cycleType_add_two σ.1).2 (by
    have h := σ.2
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h)⟩
  left_inv σ := Subtype.ext rfl
  right_inv σ := Subtype.ext rfl

private theorem fullCycle_card_add_two (n : ℕ) :
    Fintype.card
      {σ : Equiv.Perm (Fin (n + 2)) // σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))} =
      Nat.factorial (n + 1) := by
  classical
  calc
    Fintype.card
        {σ : Equiv.Perm (Fin (n + 2)) // σ.IsCycleOn (Set.univ : Set (Fin (n + 2)))} =
      Fintype.card
        ↥({σ : Equiv.Perm (Fin (n + 2)) | σ.cycleType = {n + 2}} :
          Finset (Equiv.Perm (Fin (n + 2)))) :=
      Fintype.card_congr (fullCycleEquivCycleTypeAddTwo n)
    _ = #({σ : Equiv.Perm (Fin (n + 2)) | σ.cycleType = {n + 2}} :
        Finset (Equiv.Perm (Fin (n + 2)))) := by
      apply Fintype.card_of_subtype
      intro σ
      simp
    _ = Nat.factorial (n + 1) := by
      simpa using
        (Equiv.Perm.card_of_cycleType_singleton (α := Fin (n + 2)) (n := n + 2)
          (by omega) (by simp))

private theorem cycleAssignmentKernelSum_fullCycle_one [CommSemiring R] [DecidableEq ι]
    (K : Matrix ι ι R)
    (σ : {σ : Equiv.Perm (Fin 1) // σ.IsCycleOn (Set.univ : Set (Fin 1))}) :
    cycleAssignmentKernelSum K σ.1 = Matrix.trace (K ^ 1) := by
  have hσ : σ.1 = finRotate 1 := by
    apply Equiv.ext
    intro x
    apply Fin.ext
    omega
  rw [hσ]
  simpa using cycleAssignmentKernelSum_finRotate_eq_trace K 0

private theorem fullCycle_card_one :
    Fintype.card {σ : Equiv.Perm (Fin 1) // σ.IsCycleOn (Set.univ : Set (Fin 1))} = 1 := by
  classical
  let defaultCycle :
      {σ : Equiv.Perm (Fin 1) // σ.IsCycleOn (Set.univ : Set (Fin 1))} :=
    ⟨1, by
      rw [Equiv.Perm.isCycleOn_one]
      intro x _ y _
      apply Fin.ext
      omega⟩
  letI : Unique {σ : Equiv.Perm (Fin 1) // σ.IsCycleOn (Set.univ : Set (Fin 1))} :=
    { default := defaultCycle
      uniq := fun σ => by
        apply Subtype.ext
        apply Equiv.ext
        intro x
        apply Fin.ext
        omega }
  exact Fintype.card_unique

private theorem assignmentSingleCycleKernelSum_eq_sum_cycleAssignmentKernelSum [CommSemiring R]
    (K : ι → ι → R) (m : ℕ) :
    assignmentSingleCycleKernelSum K m =
      ∑ σ : {σ : Equiv.Perm (Fin m) // σ.IsCycleOn (Set.univ : Set (Fin m))},
        cycleAssignmentKernelSum K σ.1 := by
  classical
  rw [assignmentSingleCycleKernelSum]
  simp_rw [singleCycleKernelSum_univ_eq_sum_isCycleOn]
  rw [Finset.sum_comm]
  rfl

private theorem assignmentSingleCycleKernelSum_eq_factorial_mul_trace [CommSemiring R] [DecidableEq ι]
    (K : Matrix ι ι R) (m : ℕ) (hm : 0 < m) :
    assignmentSingleCycleKernelSum K m =
      (Nat.factorial (m - 1) : R) * Matrix.trace (K ^ m) := by
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

/-- Summing the connected single-cycle contribution over all physical-index assignments gives
`ζ^(m-1) (m-1)! tr(K^m)` for positive label count `m`. This is the public trace bridge; the raw
assignment-kernel and cycle-enumeration objects remain implementation details. -/
theorem sum_singleCycleContribution_assignments_eq_factorial_mul_trace
    [CommSemiring R] [DecidableEq ι]
    (ζ : R) (K : Matrix ι ι R) (m : ℕ) (hm : 0 < m) :
    (∑ x : Fin m → ι,
      singleCycleContribution ζ (fun a b : Fin m => K (x a) (x b)) Finset.univ) =
      ζ ^ (m - 1) * ((Nat.factorial (m - 1) : R) * Matrix.trace (K ^ m)) := by
  rw [sum_singleCycleContribution_assignments_eq_pow_mul_assignmentSingleCycleKernelSum]
  rw [assignmentSingleCycleKernelSum_eq_factorial_mul_trace K m hm]

end Combinatorics
