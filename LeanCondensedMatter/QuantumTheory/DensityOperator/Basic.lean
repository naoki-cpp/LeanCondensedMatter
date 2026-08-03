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
  op : H →L[ℂ] H
  pos : op.IsPositive
  spectralTraceClass : SpectralTraceClass op
  spectralTrace_eq_one : spectralTraceClass.trace = 1

/-- A density operator's underlying operator is self-adjoint. -/
theorem DensityOperator.isSymmetric (ρ : DensityOperator H) : (ρ.op : H →ₗ[ℂ] H).IsSymmetric :=
  ρ.spectralTraceClass.symmetric

/-- The diagonal matrix elements of a density operator sum to one against any Hilbert basis. -/
theorem DensityOperator.hasSum_inner_apply_eq_one (ρ : DensityOperator H)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => (inner ℂ (d i) (ρ.op (d i)) : ℂ).re) 1 := by
  have h := ρ.spectralTraceClass.hasSum_inner_apply d
  rwa [ρ.spectralTrace_eq_one] at h

/-- The diagonal sum over any orthonormal family is bounded above by one. -/
theorem DensityOperator.sum_inner_apply_le_one (ρ : DensityOperator H)
    {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d) :
    Summable (fun i => (inner ℂ (d i) (ρ.op (d i)) : ℂ).re) ∧
      ∑' i, (inner ℂ (d i) (ρ.op (d i)) : ℂ).re ≤ 1 := by
  have h := ρ.spectralTraceClass.sum_inner_apply_le_trace ρ.pos.toLinearMap hd
  rwa [ρ.spectralTrace_eq_one] at h

/-- Each vector of the density operator's spectral eigenvector family is a unit vector. -/
theorem eigenvectorFamily_norm_eq_one (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) :
    ‖eigenvectorFamily ρ.spectralTraceClass.compact a‖ = 1 :=
  (orthonormal_eigenvectorFamily ρ.spectralTraceClass.compact ρ.isSymmetric).1 a

end QuantumTheory
