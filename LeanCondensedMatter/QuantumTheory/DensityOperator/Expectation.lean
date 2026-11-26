import LeanCondensedMatter.Analysis.Operator.HilbertBasis
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

/-- The spectral series representing the expectation of a bounded operator is summable. -/
theorem DensityOperator.summable_expectation_term (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    Summable (fun a : EigenvectorIndex ρ.op => (a.1.1 : ℂ) *
      (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
        (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)) := by
  have hnorm := eigenvectorFamily_norm_eq_one ρ
  refine Summable.of_norm_bounded
    (ρ.hasSum_abs_eigenvalues_eq_one.summable.mul_right ‖A‖) fun a => ?_
  let x := eigenvectorFamily ρ.spectralTraceClass.compact a
  rw [norm_mul, Complex.norm_real]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  change ‖(inner ℂ x (A x) : ℂ)‖ ≤ ‖A‖
  calc
    _ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg x)
    _ = ‖A‖ := by simp [x, hnorm a]

private theorem trace_comp_right_norm_le
    (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ‖(ρ.isTraceClass.comp_right A).trace‖ ≤ ‖A‖ := by
  calc
    ‖(ρ.isTraceClass.comp_right A).trace‖ ≤
        (ρ.isTraceClass.comp_right A).traceNorm :=
      (ρ.isTraceClass.comp_right A).norm_trace_le_traceNorm
    _ ≤ ‖A‖ * ρ.isTraceClass.traceNorm :=
      ρ.isTraceClass.traceNorm_comp_right_le A
    _ = ‖A‖ := by rw [ρ.traceNorm_eq_one, mul_one]

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

/-- The canonical trace expectation has the usual spectral eigenvalue expansion. -/
theorem DensityOperator.expectation_eq_spectral_tsum
    (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ρ.expectation A =
      ∑' a : EigenvectorIndex ρ.op, (a.1.1 : ℂ) *
        (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
          (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ) := by
  classical
  let hρcompact : IsCompactOperator ρ.op := ρ.spectralTraceClass.compact
  let hρsym : ρ.op.IsSymmetric := ρ.isSymmetric
  let e : EigenvectorIndex ρ.op → H := eigenvectorFamily hρcompact
  have he : Orthonormal ℂ e := by
    simpa [e] using orthonormal_eigenvectorFamily hρcompact hρsym
  obtain ⟨u, b, j, hj, hb_j⟩ := he.exists_hilbertBasis_extension_injective
  let g : u → ℂ := fun i => inner ℂ (b i) ((ρ.op * A) (b i))
  have heigen (a : EigenvectorIndex ρ.op) :
      ρ.op (e a) = (a.1.1 : ℂ) • e a := by
    simpa [e] using apply_eigenvectorFamily hρcompact a
  have hpoint (a : EigenvectorIndex ρ.op) :
      g (j a) = (a.1.1 : ℂ) * inner ℂ (e a) (A (e a)) := by
    change inner ℂ (b (j a)) ((ρ.op * A) (b (j a))) = _
    rw [hb_j, mul_apply_eq_comp]
    calc
      inner ℂ (e a) (ρ.op (A (e a))) =
          inner ℂ (ρ.op (e a)) (A (e a)) := by
        simpa only [ρ.isSelfAdjoint.adjoint_eq] using
          (ContinuousLinearMap.adjoint_inner_right ρ.op (e a) (A (e a)))
      _ = (a.1.1 : ℂ) * inner ℂ (e a) (A (e a)) := by
        rw [heigen a, inner_smul_left]
        simp
  have hzero (x : u) (hx : x ∉ Set.range j) : g x = 0 := by
    have hxker := hilbertBasis_apply_eq_zero_of_not_mem_eigenvector_range
      hρcompact hρsym b j (fun a => by simpa [e] using hb_j a) x hx
    change inner ℂ (b x) ((ρ.op * A) (b x)) = 0
    rw [mul_apply_eq_comp]
    calc
      inner ℂ (b x) (ρ.op (A (b x))) =
          inner ℂ (ρ.op (b x)) (A (b x)) := by
        simpa only [ρ.isSelfAdjoint.adjoint_eq] using
          (ContinuousLinearMap.adjoint_inner_right ρ.op (b x) (A (b x)))
      _ = 0 := by simp [hxker]
  have hfull : HasSum g (ρ.isTraceClass.comp_right A).trace := by
    change HasSum (fun i => inner ℂ (b i) ((ρ.op * A) (b i)))
      (ρ.isTraceClass.comp_right A).trace
    exact (ρ.isTraceClass.comp_right A).hasSum_trace b
  have hrestricted : HasSum
      (fun a : EigenvectorIndex ρ.op =>
        (a.1.1 : ℂ) * inner ℂ (e a) (A (e a)))
      (ρ.isTraceClass.comp_right A).trace := by
    simpa only [Function.comp_apply] using
      HasSum.congr_fun ((hj.hasSum_iff hzero).mpr hfull) fun a => (hpoint a).symm
  calc
    ρ.expectation A = (ρ.isTraceClass.comp_right A).trace := ρ.expectation_apply A
    _ = ∑' a : EigenvectorIndex ρ.op,
        (a.1.1 : ℂ) * inner ℂ (e a) (A (e a)) := hrestricted.tsum_eq.symm
    _ = ∑' a : EigenvectorIndex ρ.op, (a.1.1 : ℂ) *
        inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
          (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) := by
      simp only [e]

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
