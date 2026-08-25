import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation
import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option linter.style.header false

/-!
# Finite-dimensional diagonal expectations

This file computes a lossless diagonal expectation in an orthonormal eigenbasis of a self-adjoint
operator.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]

omit [FiniteDimensional ℂ H] in
/-- In finite dimension, the lossless diagonal expectation of a self-adjoint operator is the
weighted sum of the eigenvalues in any supplied orthonormal eigenbasis, with squared basis
coordinates as weights. -/
theorem diagonalExpectationValue_eq_sum_orthonormal_eigenbasis
    {ι : Type*} [Fintype ι] (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (b : OrthonormalBasis ι ℂ H) (E : ι → ℝ)
    (hE : ∀ i, (T : H →ₗ[ℂ] H) (b i) = (E i : ℂ) • b i) (x : H) :
    diagonalExpectationValue T hT x =
      ∑ i, E i * ‖b.repr x i‖ ^ 2 := by
  have hcoord (i : ι) : b.repr (T x) i = (E i : ℂ) * b.repr x i := by
    calc
      b.repr (T x) i = inner ℂ (b i) (T x) := b.repr_apply_apply (T x) i
      _ = inner ℂ (T (b i)) x := (hT.isSymmetric (b i) x).symm
      _ = inner ℂ ((E i : ℂ) • b i) x := by
        apply congrArg (fun y : H => inner ℂ y x)
        exact hE i
      _ = (E i : ℂ) * inner ℂ (b i) x := by
        rw [inner_smul_left]
        simp
      _ = (E i : ℂ) * b.repr x i := by rw [b.repr_apply_apply]
  apply Complex.ofReal_injective
  rw [coe_diagonalExpectationValue]
  have hinner := b.repr.inner_map_map (T x) x
  rw [PiLp.inner_apply] at hinner
  rw [← hinner]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcoord i]
  change
    inner ℂ ((E i : ℂ) * b.repr x i) (b.repr x i) =
      (E i : ℂ) * (‖b.repr x i‖ : ℂ) ^ 2
  rw [show (E i : ℂ) * b.repr x i = (E i : ℂ) • b.repr x i from rfl]
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp

/-- The supplied-basis formula specialized to Mathlib's canonical orthonormal eigenbasis. -/
theorem diagonalExpectationValue_eq_sum_eigenvectorBasis
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    diagonalExpectationValue T hT x =
      ∑ i : Fin (Module.finrank ℂ H),
        hT.isSymmetric.eigenvalues rfl i *
          ‖(hT.isSymmetric.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
  apply diagonalExpectationValue_eq_sum_orthonormal_eigenbasis
  intro i
  exact hT.isSymmetric.apply_eigenvectorBasis rfl i

end ContinuousLinearMap
