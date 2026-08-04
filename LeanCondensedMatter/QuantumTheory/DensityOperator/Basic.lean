import LeanCondensedMatter.Analysis.Operator.TraceClass.Bundled
import LeanCondensedMatter.QuantumTheory.Postulates
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Density operators

The canonical mixed-state model is a positive spectral-trace-class operator of trace one. The
definition is dimension-independent; finite-dimensional matrix-trace results are specializations
provided in `QuantumTheory/FiniteDimensional`.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A density operator is a positive spectral-trace-class operator with trace one. -/
structure DensityOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The bounded operator representing the mixed state. -/
  op : H →L[ℂ] H
  pos : op.IsPositive
  spectralTraceClass : SpectralTraceClass op
  spectralTrace_eq_one : spectralTraceClass.trace = 1

/-- A density operator's underlying operator is symmetric. -/
theorem DensityOperator.isSymmetric (ρ : DensityOperator H) : (ρ.op : H →ₗ[ℂ] H).IsSymmetric :=
  ρ.spectralTraceClass.symmetric

/-- A density operator's underlying operator is self-adjoint. -/
theorem DensityOperator.isSelfAdjoint (ρ : DensityOperator H) : IsSelfAdjoint ρ.op :=
  ρ.spectralTraceClass.isSelfAdjoint

/-- Every nonzero spectral eigenvalue of a density operator is nonnegative. -/
theorem DensityOperator.eigenvalue_nonneg (ρ : DensityOperator H)
    (a : EigenvectorIndex ρ.op) : 0 ≤ a.1.1 :=
  eigenvalue_nonneg_of_isPositive ρ.pos.toLinearMap a

/-- Every nonzero spectral eigenvalue of a density operator is at most one. -/
theorem DensityOperator.eigenvalue_le_one (ρ : DensityOperator H)
    (a : EigenvectorIndex ρ.op) : a.1.1 ≤ 1 := by
  have hsum : Summable (fun b : EigenvectorIndex ρ.op => b.1.1) :=
    ρ.spectralTraceClass.summable.congr (fun b => abs_of_nonneg (ρ.eigenvalue_nonneg b))
  have hle := hsum.le_tsum a (fun b _ => ρ.eigenvalue_nonneg b)
  have htrace := ρ.spectralTrace_eq_one
  change (∑' b : EigenvectorIndex ρ.op, b.1.1) = 1 at htrace
  rwa [htrace] at hle

/-- The lossless diagonal expectation values of a density operator sum to one against any Hilbert
basis. -/
theorem DensityOperator.hasSum_diagonalExpectationValue_eq_one (ρ : DensityOperator H)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => diagonalExpectationValue ρ.op ρ.isSelfAdjoint (d i)) 1 := by
  have h := ρ.spectralTraceClass.hasSum_diagonalExpectationValue d
  rwa [ρ.spectralTrace_eq_one] at h

/-- The lossless diagonal-expectation sum over any orthonormal family is bounded above by one. -/
theorem DensityOperator.sum_diagonalExpectationValue_le_one (ρ : DensityOperator H)
    {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d) :
    Summable (fun i => diagonalExpectationValue ρ.op ρ.isSelfAdjoint (d i)) ∧
      ∑' i, diagonalExpectationValue ρ.op ρ.isSelfAdjoint (d i) ≤ 1 := by
  have h := ρ.spectralTraceClass.sum_diagonalExpectationValue_le_trace ρ.pos hd
  rwa [ρ.spectralTrace_eq_one] at h

/-- Each vector of the density operator's spectral eigenvector family is a unit vector. -/
theorem eigenvectorFamily_norm_eq_one (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) :
    ‖eigenvectorFamily ρ.spectralTraceClass.compact a‖ = 1 :=
  (orthonormal_eigenvectorFamily ρ.spectralTraceClass.compact ρ.isSymmetric).1 a

end QuantumTheory
