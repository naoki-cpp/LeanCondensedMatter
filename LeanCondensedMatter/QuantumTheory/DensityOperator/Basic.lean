import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Bundled
import LeanCondensedMatter.QuantumTheory.Postulates
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Density operators

The canonical mixed-state model is a positive trace-class operator of trace one. Compactness,
self-adjointness, and spectral summability are derived from positivity and general trace-class
membership. The definition is dimension-independent; finite-dimensional matrix-trace results are
specializations provided in `QuantumTheory/FiniteDimensional`.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A density operator is a positive trace-class operator with trace one. -/
structure DensityOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The bounded operator representing the mixed state. -/
  op : H →L[ℂ] H
  pos : op.IsPositive
  isTraceClass : IsTraceClass op
  trace_eq_one : isTraceClass.trace = 1

attribute [simp] DensityOperator.trace_eq_one

/-- Density operators are determined by their underlying bounded operators; all remaining fields
are proof data. -/
@[ext]
theorem DensityOperator.ext {ρ σ : DensityOperator H} (h : ρ.op = σ.op) : ρ = σ := by
  cases ρ with
  | mk op hpos htrace hnorm =>
    cases σ with
    | mk op' hpos' htrace' hnorm' =>
      cases h
      rfl

/-- A density operator's underlying operator is symmetric. -/
theorem DensityOperator.isSymmetric (ρ : DensityOperator H) : (ρ.op : H →ₗ[ℂ] H).IsSymmetric :=
  ρ.pos.isSelfAdjoint.isSymmetric

/-- A density operator's underlying operator is self-adjoint. -/
theorem DensityOperator.isSelfAdjoint (ρ : DensityOperator H) : IsSelfAdjoint ρ.op :=
  ρ.pos.isSelfAdjoint

/-- The self-adjoint spectral specialization associated to a density operator. -/
theorem DensityOperator.spectralTraceClass (ρ : DensityOperator H) :
    SpectralTraceClass ρ.op where
  isTraceClass := ρ.isTraceClass
  symmetric := ρ.isSymmetric

/-- The real spectral representation of a density operator's trace is one. -/
@[simp]
theorem DensityOperator.spectralTrace_op_eq_one (ρ : DensityOperator H) :
    spectralTrace ρ.op = 1 := by
  have h := ρ.trace_eq_one
  rw [ρ.isTraceClass.trace_eq_spectralTrace ρ.isSelfAdjoint] at h
  exact_mod_cast h

/-- The general trace norm of a density operator is one. -/
@[simp]
theorem DensityOperator.traceNorm_eq_one (ρ : DensityOperator H) :
    ρ.isTraceClass.traceNorm = 1 := by
  calc
    ρ.isTraceClass.traceNorm = ρ.spectralTraceClass.isTraceClass.traceNorm :=
      IsTraceClass.traceNorm_proof_irrel ρ.isTraceClass ρ.spectralTraceClass.isTraceClass
    _ = spectralTrace ρ.op :=
      ρ.spectralTraceClass.traceNorm_eq_spectralTrace ρ.pos
    _ = 1 := ρ.spectralTrace_op_eq_one

/-- Every nonzero spectral eigenvalue of a density operator is nonnegative. -/
theorem DensityOperator.eigenvalue_nonneg (ρ : DensityOperator H)
    (a : EigenvectorIndex ρ.op) : 0 ≤ a.1.1 :=
  eigenvalue_nonneg_of_isPositive ρ.pos.toLinearMap a

/-- Every nonzero spectral eigenvalue of a density operator is at most one. -/
theorem DensityOperator.eigenvalue_le_one (ρ : DensityOperator H)
    (a : EigenvectorIndex ρ.op) : a.1.1 ≤ 1 := by
  have hsum : Summable (fun b : EigenvectorIndex ρ.op => b.1.1) :=
    (ρ.isTraceClass.hasSummableRealEigenvalues ρ.isSelfAdjoint).congr
      (fun b => abs_of_nonneg (ρ.eigenvalue_nonneg b))
  have hle := hsum.le_tsum a (fun b _ => ρ.eigenvalue_nonneg b)
  have htrace := ρ.spectralTrace_op_eq_one
  change (∑' b : EigenvectorIndex ρ.op, b.1.1) = 1 at htrace
  rwa [htrace] at hle

/-- The lossless diagonal expectation values of a density operator sum to one against any Hilbert
basis. -/
theorem DensityOperator.hasSum_diagonalExpectationValue_eq_one (ρ : DensityOperator H)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => diagonalExpectationValue ρ.op ρ.isSelfAdjoint (d i)) 1 := by
  have h := ρ.isTraceClass.hasSum_diagonalExpectationValue_eq_traceNorm ρ.pos d
  rwa [ρ.traceNorm_eq_one] at h

/-- The lossless diagonal-expectation sum over any orthonormal family is bounded above by one. -/
theorem DensityOperator.sum_diagonalExpectationValue_le_one (ρ : DensityOperator H)
    {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d) :
    Summable (fun i => diagonalExpectationValue ρ.op ρ.isSelfAdjoint (d i)) ∧
      ∑' i, diagonalExpectationValue ρ.op ρ.isSelfAdjoint (d i) ≤ 1 := by
  have h := ρ.isTraceClass.sum_diagonalExpectationValue_le_traceNorm ρ.pos hd
  rwa [ρ.traceNorm_eq_one] at h

/-- Each vector of the density operator's spectral eigenvector family is a unit vector. -/
theorem eigenvectorFamily_norm_eq_one (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) :
    ‖eigenvectorFamily ρ.isTraceClass.isCompact a‖ = 1 :=
  (orthonormal_eigenvectorFamily ρ.isTraceClass.isCompact ρ.isSymmetric).1 a

end QuantumTheory
