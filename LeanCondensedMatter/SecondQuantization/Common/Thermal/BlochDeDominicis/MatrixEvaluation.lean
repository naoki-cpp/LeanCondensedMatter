import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent

set_option linter.style.header false

/-!
# Matrix evaluation for number-conserving Bloch--de Dominicis recurrences

For a number-conserving Gaussian state, nonzero pair contractions run between two finite families
(e.g. creators and annihilators). The Wick/Bloch--de Dominicis sum is then naturally a determinant
for fermions and a permanent for bosons.

This file owns the common matrix backend:

* the bipartite contraction matrix;
* the determinant first-row recurrence, delegated to Mathlib's Laplace expansion;
* the permanent first-row recurrence, proved once from Mathlib's permutation-sum definition;
* generic induction principles identifying any matching bipartite moment recurrence with the
  corresponding determinant or permanent.

The general `Pairing` data structure remains useful for genuine Wick-diagram combinatorics. It is
not needed by the matrix-valued number-conserving evaluation backend.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- Matrix of pair contractions between two equally-sized finite operator families. -/
def bipartitePairMatrix {Left Right R : Type*} {n : ℕ}
    (pairValue : Left → Right → R) (left : Fin n → Left) (right : Fin n → Right) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => pairValue (left i) (right j)

@[simp]
theorem bipartitePairMatrix_apply {Left Right R : Type*} {n : ℕ}
    (pairValue : Left → Right → R) (left : Fin n → Left) (right : Fin n → Right)
    (i j : Fin n) :
    bipartitePairMatrix pairValue left right i j = pairValue (left i) (right j) :=
  rfl

/-- Fermionic number-conserving pairing value, represented by Mathlib's determinant. -/
def determinantBipartitePairValue {Left Right R : Type*} [CommRing R] {n : ℕ}
    (pairValue : Left → Right → R) (left : Fin n → Left) (right : Fin n → Right) : R :=
  (bipartitePairMatrix pairValue left right).det

/-- Bosonic number-conserving pairing value, represented by Mathlib's permanent. -/
def permanentBipartitePairValue {Left Right R : Type*} [CommSemiring R] {n : ℕ}
    (pairValue : Left → Right → R) (left : Fin n → Left) (right : Fin n → Right) : R :=
  (bipartitePairMatrix pairValue left right).permanent

@[simp]
theorem determinantBipartitePairValue_zero {Left Right R : Type*} [CommRing R]
    (pairValue : Left → Right → R) (left : Fin 0 → Left) (right : Fin 0 → Right) :
    determinantBipartitePairValue pairValue left right = 1 := by
  simp [determinantBipartitePairValue]

@[simp]
theorem permanentBipartitePairValue_zero {Left Right R : Type*} [CommSemiring R]
    (pairValue : Left → Right → R) (left : Fin 0 → Left) (right : Fin 0 → Right) :
    permanentBipartitePairValue pairValue left right = 1 := by
  simp [permanentBipartitePairValue, Matrix.permanent]

/-- Mathlib's row-zero Laplace expansion specialized to a contraction matrix. This is the
fermionic first-pair recursion with the remaining left field and the chosen right field removed. -/
theorem det_bipartitePairMatrix_succ_row_zero {Left Right R : Type*} [CommRing R]
    {n : ℕ} (pairValue : Left → Right → R)
    (left : Fin (n + 1) → Left) (right : Fin (n + 1) → Right) :
    (bipartitePairMatrix pairValue left right).det =
      ∑ j : Fin (n + 1),
        (-1 : R) ^ (j : ℕ) * pairValue (left 0) (right j) *
          (bipartitePairMatrix pairValue
            (fun i : Fin n => left i.succ)
            (fun i : Fin n => right (j.succAbove i))).det := by
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ext i k
  rfl

/-- Determinant recursion in the scalar wrapper used by the thermal layer. -/
theorem determinantBipartitePairValue_succ {Left Right R : Type*} [CommRing R]
    {n : ℕ} (pairValue : Left → Right → R)
    (left : Fin (n + 1) → Left) (right : Fin (n + 1) → Right) :
    determinantBipartitePairValue pairValue left right =
      ∑ j : Fin (n + 1),
        (-1 : R) ^ (j : ℕ) * pairValue (left 0) (right j) *
          determinantBipartitePairValue pairValue
            (fun i : Fin n => left i.succ)
            (fun i : Fin n => right (j.succAbove i)) := by
  exact det_bipartitePairMatrix_succ_row_zero pairValue left right

/-- The inner permutation sum appearing after fixing the image of column zero in a permanent is the
permanent of the corresponding minor. -/
private theorem permanent_decomposeFin_inner {R : Type*} [CommSemiring R]
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (p : Fin (n + 1)) :
    (∑ e : Equiv.Perm (Fin n),
        ∏ i : Fin n,
          A ((Equiv.Perm.decomposeFin.symm (p, e)) i.succ) i.succ) =
      (A.submatrix p.succAbove Fin.succ).permanent := by
  refine Fin.cases ?_ (fun k => ?_) p
  · simp only [Matrix.permanent, Equiv.Perm.decomposeFin_symm_apply_succ]
    simp
  · rw [Matrix.permanent]
    let c : Equiv.Perm (Fin n) := k.cycleRange
    refine Fintype.sum_equiv (Equiv.mulLeft c) _ _ ?_
    intro e
    apply Finset.prod_congr rfl
    intro i _
    simp [c, Equiv.Perm.decomposeFin_symm_apply_succ, Fin.succAbove_cycleRange]

/-- Permanent expansion along row zero. Mathlib currently exposes the permanent as a permutation
sum but not a Laplace-style row recurrence, so the small decomposition proof is kept here. -/
theorem Matrix.permanent_succ_row_zero {R : Type*} [CommSemiring R]
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.permanent =
      ∑ j : Fin (n + 1),
        A 0 j * (A.submatrix Fin.succ j.succAbove).permanent := by
  rw [← Matrix.permanent_transpose A, Matrix.permanent]
  have hreindex := Fintype.sum_equiv Equiv.Perm.decomposeFin
    (fun e : Equiv.Perm (Fin (n + 1)) => ∏ i : Fin (n + 1), A.transpose (e i) i)
    (fun pe : Fin (n + 1) × Equiv.Perm (Fin n) =>
      A.transpose pe.1 0 *
        ∏ i : Fin n, A.transpose ((Equiv.Perm.decomposeFin.symm pe) i.succ) i.succ)
    (fun e => by
      rw [Fin.prod_univ_succ]
      have hzero : e 0 = (Equiv.Perm.decomposeFin e).1 := by
        simpa using Equiv.Perm.decomposeFin_symm_apply_zero
          (Equiv.Perm.decomposeFin e).1 (Equiv.Perm.decomposeFin e).2
      rw [hzero])
  rw [hreindex, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Prod.fst, Matrix.transpose_apply]
  rw [← Finset.mul_sum]
  rw [permanent_decomposeFin_inner A.transpose j]
  congr 1
  simpa [Matrix.submatrix, Matrix.transpose] using
    Matrix.permanent_transpose (A.submatrix Fin.succ j.succAbove)

/-- Permanent recursion specialized to a bipartite contraction matrix. -/
theorem permanentBipartitePairValue_succ {Left Right R : Type*} [CommSemiring R]
    {n : ℕ} (pairValue : Left → Right → R)
    (left : Fin (n + 1) → Left) (right : Fin (n + 1) → Right) :
    permanentBipartitePairValue pairValue left right =
      ∑ j : Fin (n + 1),
        pairValue (left 0) (right j) *
          permanentBipartitePairValue pairValue
            (fun i : Fin n => left i.succ)
            (fun i : Fin n => right (j.succAbove i)) := by
  unfold permanentBipartitePairValue
  rw [Matrix.permanent_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ext i k
  rfl

/-- Any normalized bipartite moment satisfying the determinant first-row recurrence is exactly the
Mathlib determinant of its contraction matrix. -/
theorem moment_eq_determinantBipartitePairValue_of_recursion
    {Left Right R : Type*} [CommRing R]
    (pairValue : Left → Right → R)
    (moment : (n : ℕ) → (Fin n → Left) → (Fin n → Right) → R)
    (moment_zero : ∀ (left : Fin 0 → Left) (right : Fin 0 → Right), moment 0 left right = 1)
    (moment_succ : ∀ (n : ℕ) (left : Fin (n + 1) → Left) (right : Fin (n + 1) → Right),
      moment (n + 1) left right =
        ∑ j : Fin (n + 1),
          (-1 : R) ^ (j : ℕ) * pairValue (left 0) (right j) *
            moment n (fun i : Fin n => left i.succ)
              (fun i : Fin n => right (j.succAbove i))) :
    ∀ (n : ℕ) (left : Fin n → Left) (right : Fin n → Right),
      moment n left right = determinantBipartitePairValue pairValue left right := by
  intro n
  induction n with
  | zero =>
      intro left right
      rw [moment_zero]
      simp
  | succ n ih =>
      intro left right
      rw [moment_succ, determinantBipartitePairValue_succ]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih]

/-- Any normalized bipartite moment satisfying the permanent first-row recurrence is exactly the
Mathlib permanent of its contraction matrix. -/
theorem moment_eq_permanentBipartitePairValue_of_recursion
    {Left Right R : Type*} [CommSemiring R]
    (pairValue : Left → Right → R)
    (moment : (n : ℕ) → (Fin n → Left) → (Fin n → Right) → R)
    (moment_zero : ∀ (left : Fin 0 → Left) (right : Fin 0 → Right), moment 0 left right = 1)
    (moment_succ : ∀ (n : ℕ) (left : Fin (n + 1) → Left) (right : Fin (n + 1) → Right),
      moment (n + 1) left right =
        ∑ j : Fin (n + 1),
          pairValue (left 0) (right j) *
            moment n (fun i : Fin n => left i.succ)
              (fun i : Fin n => right (j.succAbove i))) :
    ∀ (n : ℕ) (left : Fin n → Left) (right : Fin n → Right),
      moment n left right = permanentBipartitePairValue pairValue left right := by
  intro n
  induction n with
  | zero =>
      intro left right
      rw [moment_zero]
      simp
  | succ n ih =>
      intro left right
      rw [moment_succ, permanentBipartitePairValue_succ]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih]

end BlochDeDominicis
end Common
end SecondQuantization
