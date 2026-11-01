import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace
import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.DensityOperator.Purity
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Finite-dimensional density-operator specialization

Finite dimensionality does not introduce a second density-state type. This module collects the
bridges from the canonical dimension-independent `DensityOperator` API to ordinary finite matrix
traces and finite-index corollaries.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Construct the canonical density state from a positive finite-dimensional trace-one operator. -/
noncomputable def DensityOperator.ofFiniteDimensional
    (ρ : H →L[ℂ] H) (hpos : ρ.IsPositive)
    (htrace : LinearMap.trace ℂ H (ρ : H →ₗ[ℂ] H) = 1) : DensityOperator H := by
  let hρ := isTraceClass_of_finiteDimensional ρ
  exact
    { op := ρ
      pos := hpos
      isTraceClass := hρ
      trace_eq_one := hρ.trace_eq_linearMap_trace.trans htrace }

@[simp]
theorem DensityOperator.ofFiniteDimensional_op
    (ρ : H →L[ℂ] H) (hpos : ρ.IsPositive)
    (htrace : LinearMap.trace ℂ H (ρ : H →ₗ[ℂ] H) = 1) :
    (DensityOperator.ofFiniteDimensional ρ hpos htrace).op = ρ :=
  rfl

/-- In finite dimensions, the canonical expectation agrees with the ordinary linear-map trace. -/
theorem DensityOperator.expectation_eq_linearMap_trace (ρ : DensityOperator H)
    (A : H →L[ℂ] H) :
    ρ.expectation A =
      LinearMap.trace ℂ H ((ρ.op ∘L A : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  rw [ρ.expectation_apply]
  exact (ρ.isTraceClass.comp_right A).trace_eq_linearMap_trace

/-- In finite dimensions, the ordinary trace of a density operator is one. -/
theorem DensityOperator.linearMap_trace_eq_one (ρ : DensityOperator H) :
    LinearMap.trace ℂ H (ρ.op : H →ₗ[ℂ] H) = 1 := by
  have h := (ρ.expectation_eq_linearMap_trace (ContinuousLinearMap.id ℂ H)).symm.trans
    ρ.expectation_id
  simpa using h

omit [FiniteDimensional ℂ H] in
/-- A finite diagonal expectation is the finite-index corollary of the countable Hilbert-basis
formula; no separate finite-dimensional hypothesis is needed once the finite basis is supplied. -/
theorem DensityOperator.expectation_eq_sum_diagonal {ι : Type*} [Fintype ι]
    (ρ : DensityOperator H) (A : H →L[ℂ] H) (b : OrthonormalBasis ι ℂ H)
    (w : ι → ℝ) (hρ : ∀ i, (ρ.op : H →ₗ[ℂ] H) (b i) = (w i : ℂ) • b i) :
    ρ.expectation A = ∑ i, (w i : ℂ) * inner ℂ (b i) (A (b i)) := by
  simpa [tsum_fintype] using
    ρ.expectation_eq_tsum_diagonal A b.toHilbertBasis w (fun i => by simpa using hρ i)

/-- In finite dimensions, the ordinary matrix trace `Tr(ρ²)` is the complex embedding of purity. -/
theorem DensityOperator.linearMap_trace_sq_eq_purity (ρ : DensityOperator H) :
    LinearMap.trace ℂ H
      ((ρ.op ∘L ρ.op : H →L[ℂ] H) : H →ₗ[ℂ] H) = (purity ρ : ℂ) := by
  calc
    LinearMap.trace ℂ H
        ((ρ.op ∘L ρ.op : H →L[ℂ] H) : H →ₗ[ℂ] H) = ρ.expectation ρ.op :=
      (ρ.expectation_eq_linearMap_trace ρ.op).symm
    _ = (purity ρ : ℂ) := ρ.expectation_op

end QuantumTheory
