import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation
import Mathlib.Analysis.InnerProductSpace.Spectrum

-- No project files currently carry a Mathlib-style copyright/author header; a
-- project-wide policy for this is a separate open item (see notes/conventions.md).
set_option linter.style.header false

/-!
# Finite-dimensional diagonal expectations

This file computes a lossless diagonal expectation in the orthonormal eigenbasis of a self-adjoint
operator.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]

/-- In finite dimension, the lossless diagonal expectation of a self-adjoint operator is the
weighted sum of its eigenvalues, with squared eigenbasis coordinates as weights. -/
theorem diagonalExpectationValue_eq_sum_eigenvectorBasis
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    diagonalExpectationValue T hT x =
      ∑ i : Fin (Module.finrank ℂ H),
        hT.isSymmetric.eigenvalues rfl i *
          ‖(hT.isSymmetric.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [coe_diagonalExpectationValue]
  have hinner :=
    (hT.isSymmetric.eigenvectorBasis rfl).repr.inner_map_map (T x) x
  rw [PiLp.inner_apply] at hinner
  rw [← hinner]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [hT.isSymmetric.eigenvectorBasis_apply_self_apply rfl x i]
  change
    ((hT.isSymmetric.eigenvalues rfl i : ℂ) *
        (‖(hT.isSymmetric.eigenvectorBasis rfl).repr x i‖ : ℂ) ^ 2) =
      inner ℂ
        ((hT.isSymmetric.eigenvalues rfl i : ℂ) *
          (hT.isSymmetric.eigenvectorBasis rfl).repr x i)
        ((hT.isSymmetric.eigenvectorBasis rfl).repr x i)
  rw [show (hT.isSymmetric.eigenvalues rfl i : ℂ) *
      (hT.isSymmetric.eigenvectorBasis rfl).repr x i =
      (hT.isSymmetric.eigenvalues rfl i : ℂ) •
        (hT.isSymmetric.eigenvectorBasis rfl).repr x i from rfl]
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp

end ContinuousLinearMap
