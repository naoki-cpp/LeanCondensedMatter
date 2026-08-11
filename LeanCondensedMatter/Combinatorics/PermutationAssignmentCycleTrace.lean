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
      rw [pow_succ']

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
          pathKernelWeight K ((Fin.cons p.1 p.2) 0)
            (Fin.tail (Fin.cons p.1 p.2)) ((Fin.cons p.1 p.2) 0) := by
      exact (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => ι))
        (fun x => pathKernelWeight K (x 0) (Fin.tail x) (x 0))).symm
    _ = ∑ p : ι × (Fin n → ι), pathKernelWeight K p.1 p.2 p.1 := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [Fin.cons_zero, Fin.tail_cons]
    _ = ∑ a : ι, pathKernelSum K n a a := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = Matrix.trace (K ^ (n + 1)) := by
      simp_rw [pathKernelSum_eq_pow]
      rfl

end Combinatorics
