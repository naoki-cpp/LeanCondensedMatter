/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Planar lattice Gram constraints

Planar rotations and reflections impose explicit constraints on a symmetric Gram matrix.
These criteria include reduced-cell boundaries and conventional-cell transformations.
-/

namespace LeanCondensedMatter.Crystal

namespace latticePointGroup

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable section

/-- A reflection across one integral basis axis makes the two basis vectors
orthogonal. This is the rectangular Gram-metric constraint. -/
theorem gram_offDiagonal_eq_zero_of_axisReflection
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hInv :
      let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
      A.transpose * G * A = G) :
    G 0 1 = 0 := by
  dsimp at hInv
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hInv
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
  linarith

/-- In a symmetric planar metric, invariance under the quarter-turn basis
transformation forces equal squared lengths and orthogonal basis vectors. -/
theorem gram_square_constraints_of_quarterTurn
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0)
    (hInv :
      let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
      A.transpose * G * A = G) :
    G 0 0 = G 1 1 ∧ G 0 1 = 0 := by
  dsimp at hInv
  have h00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hInv
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hInv
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  constructor <;> linarith

/-- In a symmetric planar metric, invariance under the order-six integral
rotation forces an equilateral primitive basis: equal squared lengths and
twice the off-diagonal inner product equal to their common squared length. -/
theorem gram_hexagonal_constraints_of_sixthTurn
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0)
    (hInv :
      let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 1]
      A.transpose * G * A = G) :
    G 0 0 = G 1 1 ∧ 2 * G 0 1 = G 0 0 := by
  dsimp at hInv
  have h00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hInv
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hInv
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  constructor <;> linarith


/-- For a symmetric planar Gram matrix, an integral basis-axis reflection
preserves the metric exactly when that basis is orthogonal. -/
theorem gram_axisReflection_iff (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) :
    (let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1];
      A.transpose * G * A = G) ↔ G 0 1 = 0 := by
  constructor
  · exact gram_offDiagonal_eq_zero_of_axisReflection G
  · intro h
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- For a symmetric planar metric, the quarter-turn acts isometrically exactly
when the two primitive vectors are orthogonal and have equal squared lengths. -/
theorem gram_quarterTurn_iff (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) :
    (let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0];
      A.transpose * G * A = G) ↔
      G 0 0 = G 1 1 ∧ G 0 1 = 0 := by
  constructor
  · exact gram_square_constraints_of_quarterTurn G hSymm
  · rintro ⟨hDiag, hOff⟩
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- For a symmetric planar metric, the order-six integral rotation acts
isometrically exactly when the primitive basis has the hexagonal Gram form. -/
theorem gram_sixthTurn_iff (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) :
    (let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 1];
      A.transpose * G * A = G) ↔
      G 0 0 = G 1 1 ∧ 2 * G 0 1 = G 0 0 := by
  constructor
  · exact gram_hexagonal_constraints_of_sixthTurn G hSymm
  · rintro ⟨hDiag, hOff⟩
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- The opposite orientation of the sixth-turn integral coordinate
matrix preserves a symmetric planar Gram metric exactly when the primitive
basis has equal squared lengths and a negative equilateral cross term. -/
theorem gram_sixthTurn_opposite_iff (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) :
    (let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 1];
      A.transpose * G * A = G) ↔
      G 0 0 = G 1 1 ∧ 2 * G 0 1 = -G 0 0 := by
  constructor
  · intro hInv
    dsimp at hInv
    have h00 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hInv
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hInv
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    constructor <;> linarith
  · rintro ⟨hDiag, hOff⟩
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- For a positive symmetric planar Gram metric, one of the two sixth-turn
integer matrices preserves the metric if and only if its two diagonal entries
agree and the absolute off-diagonal entry is half their common value.
The disjunction makes the hexagonal condition independent of the sign of
the primitive-basis angle. -/
theorem gram_sixthTurn_either_iff (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) (hPos : 0 < G 0 0) :
    ((let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 1];
        A.transpose * G * A = G) ∨
      (let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 1];
        A.transpose * G * A = G)) ↔
      G 0 0 = G 1 1 ∧ 2 * |G 0 1| = G 0 0 := by
  constructor
  · rintro (hInv | hInv)
    · obtain ⟨hDiag, hOff⟩ := (gram_sixthTurn_iff G hSymm).mp hInv
      have hNonneg : 0 ≤ G 0 1 := by linarith
      refine ⟨hDiag, ?_⟩
      rw [abs_of_nonneg hNonneg]
      exact hOff
    · obtain ⟨hDiag, hOff⟩ := (gram_sixthTurn_opposite_iff G hSymm).mp hInv
      have hNonpos : G 0 1 ≤ 0 := by linarith
      refine ⟨hDiag, ?_⟩
      rw [abs_of_nonpos hNonpos]
      linarith
  · rintro ⟨hDiag, hAbs⟩
    rcases le_total (0 : ℝ) (G 0 1) with hNonneg | hNonpos
    · left
      apply (gram_sixthTurn_iff G hSymm).mpr
      refine ⟨hDiag, ?_⟩
      rwa [abs_of_nonneg hNonneg] at hAbs
    · right
      apply (gram_sixthTurn_opposite_iff G hSymm).mpr
      refine ⟨hDiag, ?_⟩
      rw [abs_of_nonpos hNonpos] at hAbs
      linarith

/-- On the Gauss-reduced metric region, a sixth-turn integral symmetry exists
in one of the two orientations exactly on the boundary where the shorter
primitive vector is tied in squared length with one of the sum/difference
vectors. Indeed their smaller squared length is
`G₀₀ + G₁₁ - 2 * |G₀₁|`. -/
theorem gram_reduced_sixthTurn_iff_boundary
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0)
    (hPos : 0 < G 0 0)
    (hDiag : G 0 0 ≤ G 1 1)
    (hOff : 2 * |G 0 1| ≤ G 0 0) :
    ((let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 1];
        A.transpose * G * A = G) ∨
      (let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 1];
        A.transpose * G * A = G)) ↔
      G 0 0 + G 1 1 - 2 * |G 0 1| = G 0 0 := by
  rw [gram_sixthTurn_either_iff G hSymm hPos]
  constructor
  · rintro ⟨hEq, hAbs⟩
    linarith
  · intro hBoundary
    constructor <;> linarith

/-- Swapping two primitive basis vectors preserves a symmetric Gram matrix
exactly when they have equal squared lengths. This is the rhombic primitive-basis
condition relevant to the centered-rectangular Bravais class. It is not by
itself an exhaustive characterization of that class. -/
theorem gram_basisSwap_iff (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) :
    (let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0];
      A.transpose * G * A = G) ↔ G 0 0 = G 1 1 := by
  constructor
  · intro hInv
    dsimp at hInv
    have h00 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hInv
    have heq : G 1 1 = G 0 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00
    exact heq.symm
  · intro hDiag
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- The shear-reflection `e₁ ↦ e₁`, `e₂ ↦ e₁ - e₂` is a Gram
isometry exactly when the primitive vectors meet the positive edge
`2 G₀₁ = G₀₀` of the Gauss size-reduction inequality. The integral
matrix is involutive and has determinant `-1`. -/
theorem gram_shearReflection_positive_iff
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hSymm : G 0 1 = G 1 0) :
    (let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, -1];
      A.transpose * G * A = G) ↔ 2 * G 0 1 = G 0 0 := by
  constructor
  · intro hInv
    dsimp at hInv
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hInv
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
    linarith
  · intro hOff
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- The opposite shear-reflection `e₂ ↦ -e₁ - e₂` is an isometry
exactly on the negative size-reduction edge `2 G₀₁ = -G₀₀`. -/
theorem gram_shearReflection_negative_iff
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hSymm : G 0 1 = G 1 0) :
    (let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 0, -1];
      A.transpose * G * A = G) ↔ 2 * G 0 1 = -G 0 0 := by
  constructor
  · intro hInv
    dsimp at hInv
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hInv
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
    linarith
  · intro hOff
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- The two integral shear-reflections jointly characterize the
sign-independent edge `2 |G₀₁| = G₀₀` for positive primitive metrics. -/
theorem gram_shearReflection_either_iff
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) (hPos : 0 < G 0 0) :
    ((let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, -1];
        A.transpose * G * A = G) ∨
      (let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 0, -1];
        A.transpose * G * A = G)) ↔
      2 * |G 0 1| = G 0 0 := by
  constructor
  · rintro (hInv | hInv)
    · have hOff := (gram_shearReflection_positive_iff G hSymm).mp hInv
      have hNonneg : 0 ≤ G 0 1 := by linarith
      rw [abs_of_nonneg hNonneg]
      exact hOff
    · have hOff := (gram_shearReflection_negative_iff G hSymm).mp hInv
      have hNonpos : G 0 1 ≤ 0 := by linarith
      rw [abs_of_nonpos hNonpos]
      linarith
  · intro hAbs
    rcases le_total (0 : ℝ) (G 0 1) with hNonneg | hNonpos
    · left
      apply (gram_shearReflection_positive_iff G hSymm).mpr
      rwa [abs_of_nonneg hNonneg] at hAbs
    · right
      apply (gram_shearReflection_negative_iff G hSymm).mpr
      rw [abs_of_nonpos hNonpos] at hAbs
      linarith

/-- Three explicitly exhibited kinds of integral reflection witness pick out
the three walls of the planar Gauss-reduced metric region: an orthogonal
primitive basis, equal primitive lengths, or the size-reduction edge.

The result classifies these *standard witnesses*, not all possible reflection
matrices up to integral conjugacy. That completeness statement requires an
additional arithmetic argument. -/
theorem gram_standard_reflection_walls_iff
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) (hPos : 0 < G 0 0) :
    ((let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1];
        A.transpose * G * A = G) ∨
      (let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0];
        A.transpose * G * A = G) ∨
      ((let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, -1];
          A.transpose * G * A = G) ∨
        (let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 0, -1];
          A.transpose * G * A = G))) ↔
      G 0 1 = 0 ∨ G 0 0 = G 1 1 ∨ 2 * |G 0 1| = G 0 0 := by
  rw [gram_axisReflection_iff G hSymm, gram_basisSwap_iff G hSymm,
    gram_shearReflection_either_iff G hSymm hPos]

/-- On the positive Gauss size-reduction edge, the index-two conventional
cell with columns `e₁` and `2 e₂ - e₁` is orthogonal. Conversely,
orthogonality of this conventional cell forces that edge condition.
Unlike an integral primitive basis change, this matrix has determinant `2`. -/
theorem gram_shiftedConventionalCell_diagonal_iff
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hSymm : G 0 1 = G 1 0) :
    (let S : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 0, 2];
     S.transpose * G * S =
       !![G 0 0, 0; 0, 4 * G 1 1 - G 0 0]) ↔
      2 * G 0 1 = G 0 0 := by
  constructor
  · intro h
    dsimp at h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
    linarith
  · intro hEdge
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- An integral matrix of determinant minus one fixing the first
primitive basis vector is necessarily a shear-reflection. No metric
hypothesis is needed for this arithmetic normal form. -/
theorem integer_fixedFirst_reflection_normalform
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hFirst : A 0 0 = 1 ∧ A 1 0 = 0)
    (hDet : A.det = -1) :
    A = !![1, A 0 1; 0, -1] := by
  have h11 : A 1 1 = -1 := by
    simpa [Matrix.det_fin_two, hFirst.1, hFirst.2] using hDet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hFirst.1, hFirst.2, h11]

/-- For an integral reflection fixing the first primitive vector,
Gram preservation forces twice the off-diagonal coefficient to be an
integer multiple of the first squared length. -/
theorem gram_fixedFirst_reflection_relation
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hFirst : A 0 0 = 1 ∧ A 1 0 = 0)
    (hDet : A.det = -1)
    (hInv :
      (A.map (Int.cast : ℤ → ℝ)).transpose * G *
        (A.map (Int.cast : ℤ → ℝ)) = G) :
    2 * G 0 1 = (A 0 1 : ℝ) * G 0 0 := by
  have h11 : A 1 1 = -1 := by
    have hNormal := integer_fixedFirst_reflection_normalform A hFirst hDet
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) hNormal
    simpa using h
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hInv
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
    hFirst.1, hFirst.2, h11] at h01
  linarith

/-- Every determinant-minus-one integral Gram symmetry fixing the first
primitive vector of a Gauss-reduced basis is one of the three standard
reflections: axis reflection or a positive/negative unit shear-reflection.

This is an exhaustive statement within the *fixed-first-vector* class;
an arbitrary reflection need not fix that particular primitive vector. -/
theorem gram_reduced_fixedFirst_reflection_cases
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hPos : 0 < G 0 0)
    (hOff : 2 * |G 0 1| ≤ G 0 0)
    (hFirst : A 0 0 = 1 ∧ A 1 0 = 0)
    (hDet : A.det = -1)
    (hInv :
      (A.map (Int.cast : ℤ → ℝ)).transpose * G *
        (A.map (Int.cast : ℤ → ℝ)) = G) :
    (A 0 1 = -1 ∧ 2 * G 0 1 = -G 0 0) ∨
      (A 0 1 = 0 ∧ G 0 1 = 0) ∨
      (A 0 1 = 1 ∧ 2 * G 0 1 = G 0 0) := by
  have hRelation :=
    gram_fixedFirst_reflection_relation G A hFirst hDet hInv
  have hBound : |G 0 1| ≤ G 0 0 / 2 := by linarith
  have hAbs := abs_le.mp hBound
  have hLower : -(G 0 0) ≤ (A 0 1 : ℝ) * G 0 0 := by
    rw [← hRelation]
    linarith [hAbs.1]
  have hUpper : (A 0 1 : ℝ) * G 0 0 ≤ G 0 0 := by
    rw [← hRelation]
    linarith [hAbs.2]
  have hIntBound : (-1 : ℝ) ≤ (A 0 1 : ℝ) ∧ (A 0 1 : ℝ) ≤ 1 := by
    constructor
    · apply (mul_le_mul_iff_of_pos_right hPos).mp
      nlinarith [hLower]
    · apply (mul_le_mul_iff_of_pos_right hPos).mp
      nlinarith [hUpper]
  have hZBound : (-1 : ℤ) ≤ A 0 1 ∧ A 0 1 ≤ 1 := by
    exact_mod_cast hIntBound
  have hCases : A 0 1 = -1 ∨ A 0 1 = 0 ∨ A 0 1 = 1 := by
    omega
  rcases hCases with hNeg | hZero | hOne
  · left
    constructor
    · exact hNeg
    · simpa [hNeg] using hRelation
  · right
    left
    constructor
    · exact hZero
    · have h := hRelation
      rw [hZero] at h
      norm_num at h ⊢
      linarith
  · right
    right
    constructor
    · exact hOne
    · simpa [hOne] using hRelation

/-- Conjugating a shear-reflection by an integral shear changes its shear
coefficient by an even integer. This arithmetic identity exposes the
parity invariant distinguishing the two integral reflection classes. -/
theorem integer_fixedFirst_reflection_shear_conjugation (k n : ℤ) :
    (!![1, -n; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) *
        !![1, k; 0, -1] * !![1, n; 0, 1] =
      !![1, k + 2 * n; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- Every integer reflection fixing the first vector is shear-conjugate
to one with coefficient zero or one. Thus the integer conjugacy class
depends only on the shear coefficient modulo two. -/
theorem integer_fixedFirst_reflection_parity_normalform (k : ℤ) :
    ∃ n : ℤ,
      (!![1, -n; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) *
          !![1, k; 0, -1] * !![1, n; 0, 1] =
        !![1, k % 2; 0, -1] ∧
      (k % 2 = 0 ∨ k % 2 = 1) := by
  refine ⟨-(k / 2), ?_, ?_⟩
  · rw [integer_fixedFirst_reflection_shear_conjugation]
    have hk : k + 2 * (-(k / 2)) = k % 2 := by omega
    rw [hk]
  · omega

/-- In dimension two, an integral matrix with trace zero and
determinant minus one is an involution. This is a matrix identity over
`ℤ`, independently of the ambient real Gram metric. -/
theorem integer_trace_zero_det_neg_one_sq
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hTrace : A.trace = 0) (hDet : A.det = -1) :
    A * A = 1 := by
  have ht : A 0 0 + A 1 1 = 0 := by
    simpa [Matrix.trace_fin_two] using hTrace
  have hd : A 1 1 = -(A 0 0) := by omega
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = -1 := by
    simpa [Matrix.det_fin_two] using hDet
  have hquad : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by
    rw [hd] at hdet
    nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hd] <;> nlinarith [hquad]

/-- A trace-zero determinant-minus-one integral matrix has a nonzero
integer vector fixed by its action. The eigenvector is constructed
directly from the entries, without extending scalars to the reals.
A later primitive-vector completion will turn this into a unimodular
change of basis for arbitrary integral reflections. -/
theorem integer_trace_zero_det_neg_one_fixed_vector
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hTrace : A.trace = 0) (hDet : A.det = -1) :
    ∃ v : Fin 2 → ℤ, v ≠ 0 ∧ A.mulVec v = v := by
  have ht : A 0 0 + A 1 1 = 0 := by
    simpa [Matrix.trace_fin_two] using hTrace
  have hd : A 1 1 = -(A 0 0) := by omega
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = -1 := by
    simpa [Matrix.det_fin_two] using hDet
  have hquad : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by
    rw [hd] at hdet
    nlinarith
  by_cases ha : A 0 0 = -1
  · let v : Fin 2 → ℤ := ![A 0 1, 1 - A 0 0]
    refine ⟨v, ?_, ?_⟩
    · intro hv
      have hv1 := congrArg (fun w : Fin 2 → ℤ => w 1) hv
      change 1 - A 0 0 = 0 at hv1
      omega
    · funext i
      fin_cases i
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        change A 0 0 * A 0 1 + A 0 1 * (1 - A 0 0) = A 0 1
        ring
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        change A 1 0 * A 0 1 + A 1 1 * (1 - A 0 0) = 1 - A 0 0
        rw [hd]
        nlinarith [hquad]
  · let v : Fin 2 → ℤ := ![A 0 0 + 1, A 1 0]
    refine ⟨v, ?_, ?_⟩
    · intro hv
      have hv0 := congrArg (fun w : Fin 2 → ℤ => w 0) hv
      change A 0 0 + 1 = 0 at hv0
      omega
    · funext i
      fin_cases i
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        change A 0 0 * (A 0 0 + 1) + A 0 1 * A 1 0 = A 0 0 + 1
        nlinarith [hquad]
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        change A 1 0 * (A 0 0 + 1) + A 1 1 * A 1 0 = A 1 0
        rw [hd]
        ring

/-- The same integral reflection also has a nonzero integer vector
reversed by its action. The two eigendirections provide the arithmetic
starting point for classifying arbitrary planar reflections. -/
theorem integer_trace_zero_det_neg_one_reversed_vector
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hTrace : A.trace = 0) (hDet : A.det = -1) :
    ∃ v : Fin 2 → ℤ, v ≠ 0 ∧ A.mulVec v = -v := by
  have ht : (-A).trace = 0 := by
    have ht := hTrace
    simp only [Matrix.trace_fin_two, Matrix.neg_apply] at ht ⊢
    omega
  have hd : (-A).det = -1 := by
    simpa [Matrix.det_fin_two] using hDet
  obtain ⟨v, hv, hAv⟩ := integer_trace_zero_det_neg_one_fixed_vector (-A) ht hd
  refine ⟨v, hv, ?_⟩
  funext i
  have hi := congrFun hAv i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hi ⊢
  linarith

/-- The sum and difference of two primitive lattice vectors form an orthogonal
conventional cell exactly when the vectors have equal squared lengths.

For a symmetric Gram metric `G`, the columns of `S = !![1, 1; 1, -1]`
are the sum and difference of the primitive basis vectors. When `G₀₀ = G₁₁`,
the conventional squared lengths are `2 * (G₀₀ + G₀₁)` and
`2 * (G₀₀ - G₀₁)`. This is the metric relation underlying the
centered-rectangular Bravais class. The matrix `S` has determinant `-2`,
so this conventional cell is not an integral primitive basis change. -/
theorem gram_sumDiff_diagonal_iff (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) :
    (let S : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1];
     S.transpose * G * S =
       !![2 * (G 0 0 + G 0 1), 0;
          0, 2 * (G 0 0 - G 0 1)]) ↔ G 0 0 = G 1 1 := by
  constructor
  · intro h
    dsimp at h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
    linarith
  · intro hDiag
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

end

end latticePointGroup

end LeanCondensedMatter.Crystal
