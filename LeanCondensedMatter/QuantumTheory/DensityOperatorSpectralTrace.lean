import LeanCondensedMatter.Analysis.Operator.TraceClass.Bundled
import LeanCondensedMatter.QuantumTheory.DensityOperatorTraceClass

set_option linter.style.header false

/-!
# Bundled spectral-trace API for density operators

An infinite-dimensional `QuantumTheory.TraceClass.DensityOperator` already carries positivity,
compactness, and summability of its nonzero real eigenvalues. This module packages those fields as
`ContinuousLinearMap.SpectralTraceClass` data and exposes the normalization consequences through
the bundled operator API, without changing the existing density-operator structure or its public
fields.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bundled compact, symmetric, spectrally summable data carried by a density operator. -/
def DensityOperator.spectralTraceClass (ρ : DensityOperator H) :
    ContinuousLinearMap.SpectralTraceClass ρ.op :=
  ContinuousLinearMap.SpectralTraceClass.ofPositive ρ.compact ρ.pos ρ.traceClass

/-- The bundled spectral trace agrees with the density operator's existing unbundled trace. -/
@[simp] theorem DensityOperator.spectralTraceClass_trace (ρ : DensityOperator H) :
    ρ.spectralTraceClass.trace = ContinuousLinearMap.trace ρ.traceClass := by
  rfl

/-- A density operator's bundled spectral trace is normalized to `1`. -/
@[simp] theorem DensityOperator.spectralTrace_eq_one (ρ : DensityOperator H) :
    ρ.spectralTraceClass.trace = 1 := by
  rw [ρ.spectralTraceClass_trace]
  exact ρ.trace_eq_one

/-- The diagonal matrix elements of a density operator sum to `1` against any Hilbert basis. -/
theorem DensityOperator.hasSum_inner_apply_eq_one (ρ : DensityOperator H)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => (inner ℂ (d i) (ρ.op (d i)) : ℂ).re) 1 := by
  simpa using ρ.spectralTraceClass.hasSum_inner_apply d

/-- The diagonal sum over any orthonormal family is bounded above by `1`. -/
theorem DensityOperator.sum_inner_apply_le_one (ρ : DensityOperator H)
    {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d) :
    Summable (fun i => (inner ℂ (d i) (ρ.op (d i)) : ℂ).re) ∧
      ∑' i, (inner ℂ (d i) (ρ.op (d i)) : ℂ).re ≤ 1 := by
  simpa using ρ.spectralTraceClass.sum_inner_apply_le_trace ρ.pos.toLinearMap hd

end QuantumTheory.TraceClass
