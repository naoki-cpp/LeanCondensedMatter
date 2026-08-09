import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent

set_option linter.style.header false

/-!
# Matrix evaluation for number-conserving Bloch--de Dominicis recurrences

For a number-conserving Gaussian state, nonzero pair contractions run between two finite families
(e.g. creators and annihilators).  The Wick/Bloch--de Dominicis sum is then naturally a determinant
for fermions and a permanent for bosons.  This file packages the common contraction matrix and the
Mathlib determinant Laplace expansion in the exact `Fin.succ`/`succAbove` shape used by the thermal
first-pair recurrence.

The general perfect-pairing representation remains available for diagrammatics and for future
anomalous Gaussian states.  This module is the matrix-valued backend for the number-conserving
specialization.
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

/-- Mathlib's row-zero Laplace expansion specialized to a contraction matrix.  This is the
fermionic first-pair recursion with the remaining creator and the chosen annihilator removed. -/
theorem det_bipartitePairMatrix_succ_row_zero {Left Right R : Type*} [CommRing R]
    {n : ℕ} (pairValue : Left → Right → R)
    (left : Fin (n + 1) → Left) (right : Fin (n + 1) → Right) :
    (bipartitePairMatrix pairValue left right).det =
      ∑ j : Fin (n + 1),
        (-1 : R) ^ (j : ℕ) * pairValue (left 0) (right j) *
          (bipartitePairMatrix pairValue
            (fun i : Fin n => left i.succ)
            (fun i : Fin n => right (j.succAbove i))).det := by
  simpa [bipartitePairMatrix] using
    Matrix.det_succ_row_zero (bipartitePairMatrix pairValue left right)

/-- Bosonic number-conserving pairing value, represented by Mathlib's permanent. -/
def permanentBipartitePairValue {Left Right R : Type*} [CommSemiring R] {n : ℕ}
    (pairValue : Left → Right → R) (left : Fin n → Left) (right : Fin n → Right) : R :=
  (bipartitePairMatrix pairValue left right).permanent

/-- Fermionic number-conserving pairing value, represented by Mathlib's determinant. -/
def determinantBipartitePairValue {Left Right R : Type*} [CommRing R] {n : ℕ}
    (pairValue : Left → Right → R) (left : Fin n → Left) (right : Fin n → Right) : R :=
  (bipartitePairMatrix pairValue left right).det

@[simp]
theorem determinantBipartitePairValue_zero {Left Right R : Type*} [CommRing R]
    (pairValue : Left → Right → R) (left : Fin 0 → Left) (right : Fin 0 → Right) :
    determinantBipartitePairValue pairValue left right = 1 := by
  simp [determinantBipartitePairValue]

@[simp]
theorem permanentBipartitePairValue_zero {Left Right R : Type*} [CommSemiring R]
    (pairValue : Left → Right → R) (left : Fin 0 → Left) (right : Fin 0 → Right) :
    permanentBipartitePairValue pairValue left right = 1 := by
  simp [permanentBipartitePairValue]

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

end BlochDeDominicis
end Common
end SecondQuantization
