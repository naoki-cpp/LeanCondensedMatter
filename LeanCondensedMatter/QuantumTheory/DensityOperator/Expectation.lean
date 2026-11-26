import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral
import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops
import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic

/-!
# Expectations of bounded operators

A density operator defines a normalized continuous complex-linear functional on bounded operators.
The canonical definition is the general trace-class trace `Tr(ρA)`. The spectral eigenvalue
expansion is derived as a representation theorem.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem trace_comp_right_norm_le
    (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ‖(ρ.isTraceClass.comp_right A).trace‖ ≤ ‖A‖ := by
  simpa only [ρ.traceNorm_eq_one, mul_one] using
    ρ.isTraceClass.norm_trace_comp_right_le A

/-- The normalized complex expectation functional associated with a density operator.
Its canonical value on `A` is the general trace-class trace `Tr(ρA)`. -/
noncomputable def DensityOperator.expectation (ρ : DensityOperator H) :
    (H →L[ℂ] H) →L[ℂ] ℂ :=
  IsBoundedLinearMap.toContinuousLinearMap
    (fun A : H →L[ℂ] H => (ρ.isTraceClass.comp_right A).trace)
    { map_add := fun A B => by
        simpa only [mul_add] using
          (ρ.isTraceClass.comp_right A).trace_add (ρ.isTraceClass.comp_right B)
      map_smul := fun c A => by
        simpa only [smul_eq_mul, mul_smul_comm] using
          (ρ.isTraceClass.comp_right A).trace_smul c
      bound := ⟨1, zero_lt_one, fun A => by simpa using trace_comp_right_norm_le ρ A⟩ }

/-- The canonical expectation is the general trace-class trace `Tr(ρA)`. -/
theorem DensityOperator.expectation_apply (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ρ.expectation A = (ρ.isTraceClass.comp_right A).trace :=
  rfl

/-- A scalar intertwining relation with the density operator yields the corresponding
expectation rotation by cyclicity of the trace. No Gibbs or ladder-operator assumptions are needed. -/
theorem DensityOperator.expectation_comp_rotate_of_intertwine
    (ρ : DensityOperator H) (C A : H →L[ℂ] H) (q : ℂ)
    (hcomm : ρ.op.comp C = q • (C.comp ρ.op)) :
    ρ.expectation (C.comp A) = q * ρ.expectation (A.comp C) := by
  change ρ.op * C = q • (C * ρ.op) at hcomm
  rw [DensityOperator.expectation_apply, DensityOperator.expectation_apply]
  calc
    _ = (((ρ.isTraceClass.comp_right A).comp_left C).smul q).trace := by
      apply IsTraceClass.trace_congr
      change ρ.op * (C * A) = q • (C * (ρ.op * A))
      rw [← mul_assoc, hcomm, smul_mul_assoc, mul_assoc]
    _ = q * ((ρ.isTraceClass.comp_right A).comp_left C).trace :=
      ((ρ.isTraceClass.comp_right A).comp_left C).trace_smul q
    _ = _ := by
      simpa only [← ContinuousLinearMap.mul_def, mul_assoc] using
        congrArg (fun z : ℂ => q * z) ((ρ.isTraceClass.comp_right A).trace_comp_comm C).symm

/-- The spectral series of a bounded operator sums to its density-state expectation. -/
theorem DensityOperator.hasSum_expectation_term (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    HasSum (fun a : EigenvectorIndex ρ.op => (a.1.1 : ℂ) *
      (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
        (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)) (ρ.expectation A) := by
  rw [ρ.expectation_apply]
  exact ρ.isTraceClass.hasSum_trace_comp_right_eigenvector ρ.isSelfAdjoint A

/-- The canonical trace expectation has the usual spectral eigenvalue expansion. -/
theorem DensityOperator.expectation_eq_spectral_tsum
    (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ρ.expectation A =
      ∑' a : EigenvectorIndex ρ.op, (a.1.1 : ℂ) *
        (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
          (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ) :=
  (ρ.hasSum_expectation_term A).tsum_eq.symm

/-- Expectations are contractive in the operator norm. -/
theorem DensityOperator.norm_expectation_le (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ‖ρ.expectation A‖ ≤ ‖A‖ :=
  trace_comp_right_norm_le ρ A

/-- The expectation of the identity operator is one. -/
@[simp]
theorem DensityOperator.expectation_id (ρ : DensityOperator H) :
    ρ.expectation (ContinuousLinearMap.id ℂ H) = 1 := by
  rw [ρ.expectation_apply]
  calc
    (ρ.isTraceClass.comp_right (ContinuousLinearMap.id ℂ H)).trace =
        ρ.isTraceClass.trace := by
      apply IsTraceClass.trace_congr
      ext x
      rw [mul_apply_eq_comp, ContinuousLinearMap.id_apply]
    _ = 1 := ρ.trace_eq_one

end QuantumTheory
