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

omit [CompleteSpace H] in
private theorem norm_inner_apply_le_opNorm_of_norm_eq_one
    (A : H →L[ℂ] H) {x : H} (hx : ‖x‖ = 1) :
    ‖(inner ℂ x (A x) : ℂ)‖ ≤ ‖A‖ := by
  calc
    ‖(inner ℂ x (A x) : ℂ)‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by
      gcongr
      exact A.le_opNorm _
    _ = ‖A‖ := by rw [hx]; ring

/-- The spectral series representing the expectation of a bounded operator is summable. -/
theorem DensityOperator.summable_expectation_term (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    Summable (fun a : EigenvectorIndex ρ.op => (a.1.1 : ℂ) *
      (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
        (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)) := by
  have hnorm := eigenvectorFamily_norm_eq_one ρ
  refine Summable.of_norm_bounded
    (ρ.spectralTraceClass.summable.mul_right ‖A‖) fun a => ?_
  have hle := norm_inner_apply_le_opNorm_of_norm_eq_one A (hnorm a)
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)

/-- The absolute eigenvalue weights of a density operator sum to one. -/
theorem DensityOperator.hasSum_abs_eigenvalues_eq_one (ρ : DensityOperator H) :
    HasSum (fun a : EigenvectorIndex ρ.op => |a.1.1|) 1 := by
  have hsum : HasSum (fun a : EigenvectorIndex ρ.op => a.1.1) 1 := by
    have h := (summable_eigenvectorIndex ρ.spectralTraceClass.summable).hasSum
    have htrace : (∑' a : EigenvectorIndex ρ.op, a.1.1) = 1 := by
      simpa [spectralTrace] using ρ.spectralTrace_op_eq_one
    rwa [htrace] at h
  exact HasSum.congr_fun hsum fun a =>
    abs_of_nonneg (eigenvalue_nonneg_of_isPositive ρ.pos.toLinearMap a)

/-- The unbundled canonical trace expectation used to construct `DensityOperator.expectation`. -/
private noncomputable def densityExpectationTrace
    (ρ : DensityOperator H) (A : H →L[ℂ] H) : ℂ :=
  (ρ.isTraceClass.comp_right A).trace

private theorem densityExpectationTrace_add
    (ρ : DensityOperator H) (A B : H →L[ℂ] H) :
    densityExpectationTrace ρ (A + B) =
      densityExpectationTrace ρ A + densityExpectationTrace ρ B := by
  unfold densityExpectationTrace
  simpa only [mul_add] using
    (ρ.isTraceClass.comp_right A).trace_add (ρ.isTraceClass.comp_right B)

private theorem densityExpectationTrace_smul
    (ρ : DensityOperator H) (c : ℂ) (A : H →L[ℂ] H) :
    densityExpectationTrace ρ (c • A) = c * densityExpectationTrace ρ A := by
  unfold densityExpectationTrace
  simpa only [mul_smul_comm] using
    (ρ.isTraceClass.comp_right A).trace_smul c

private theorem densityExpectationTrace_norm_le
    (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ‖densityExpectationTrace ρ A‖ ≤ ‖A‖ := by
  unfold densityExpectationTrace
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
    (fun A : H →L[ℂ] H => densityExpectationTrace ρ A)
    { map_add := densityExpectationTrace_add ρ
      map_smul := fun c A => by
        simpa only [smul_eq_mul] using densityExpectationTrace_smul ρ c A
      bound := ⟨1, zero_lt_one, fun A => by simpa using densityExpectationTrace_norm_le ρ A⟩ }

/-- The canonical expectation is the general trace-class trace `Tr(ρA)`. -/
theorem DensityOperator.expectation_apply (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ρ.expectation A = (ρ.isTraceClass.comp_right A).trace :=
  rfl

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
  obtain ⟨u, b, hsub, hb⟩ := he.toSubtypeRange.exists_hilbertBasis_extension
  let j : EigenvectorIndex ρ.op → u := fun a => ⟨e a, hsub ⟨a, rfl⟩⟩
  have hj : Function.Injective j := by
    intro a a' haa'
    apply he.linearIndependent.injective
    exact congrArg Subtype.val haa'
  let g : u → ℂ := fun i => inner ℂ (b i) ((ρ.op * A) (b i))
  have hb_j (a : EigenvectorIndex ρ.op) : b (j a) = e a := by
    rw [hb]
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
  densityExpectationTrace_norm_le ρ A

/-- The expectation of the identity operator is one. -/
@[simp]
theorem DensityOperator.expectation_id (ρ : DensityOperator H) :
    ρ.expectation (ContinuousLinearMap.id ℂ H) = 1 := by
  rw [ρ.expectation_eq_spectral_tsum]
  calc
    (∑' a : EigenvectorIndex ρ.op, (a.1.1 : ℂ) *
      inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
        ((ContinuousLinearMap.id ℂ H) (eigenvectorFamily ρ.spectralTraceClass.compact a))) =
        ∑' a : EigenvectorIndex ρ.op, (a.1.1 : ℂ) := by
      apply tsum_congr
      intro a
      rw [ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K,
        eigenvectorFamily_norm_eq_one ρ a]
      norm_num
    _ = 1 := by
      have htrace : (∑' a : EigenvectorIndex ρ.op, a.1.1) = 1 := by
        simpa [spectralTrace] using ρ.spectralTrace_op_eq_one
      exact_mod_cast htrace

end QuantumTheory
