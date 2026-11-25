import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace
import LeanCondensedMatter.Analysis.Operator.AdjointConjugation

set_option linter.style.header false

/-!
# Operations on general trace-class operators

Trace-class membership is closed under the standard linear and bounded-composition operations.
The canonical complex trace is linear under the corresponding additive and scalar operations,
and cyclic when one factor is trace class and the other is bounded.
Bounded adjoint conjugation preserves trace-class membership; if `U† U = 1`, it preserves
trace without requiring surjectivity of `U`.
The trace norm satisfies the corresponding scalar and adjoint identities, bounded-composition
estimates, triangle inequality, and bound on the modulus of the complex trace.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The zero bounded operator is trace class. -/
theorem isTraceClass_zero : IsTraceClass (0 : H →L[ℂ] H) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  apply (isTraceClass_iff_isTraceClassWrt d (0 : H →L[ℂ] H)).mpr
  rw [IsTraceClassWrt]
  simpa only [CFC.abs_zero] using
    (summable_zero.congr fun i =>
      (diagonalExpectationValue_zero
        (show IsSelfAdjoint (0 : H →L[ℂ] H) by simp) (d i)).symm)


/-- Trace-class membership is closed under complex scalar multiplication. -/
theorem IsTraceClass.smul {T : H →L[ℂ] H} (hT : IsTraceClass T) (c : ℂ) :
    IsTraceClass (c • T) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  apply (isTraceClass_iff_isTraceClassWrt d (c • T)).mpr
  rw [IsTraceClassWrt]
  have hsum := (isTraceClass_iff_isTraceClassWrt d T).mp hT
  rw [IsTraceClassWrt] at hsum
  exact (hsum.mul_left ‖c‖).congr fun i => (diagonalExpectationValue_abs_smul c T (d i)).symm

/-- Trace-class membership is closed under negation. -/
theorem IsTraceClass.neg {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass (-T) := by
  simpa only [neg_one_smul] using hT.smul (-1 : ℂ)

/-- Taking the adjoint preserves trace-class membership. -/
theorem IsTraceClass.adjoint {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass (ContinuousLinearMap.adjoint T) := by
  obtain ⟨A, B, hA, hB, hfactor⟩ :=
    (isTraceClass_iff_exists_hilbertSchmidt_factorization (T := T)).mp hT
  apply (isTraceClass_iff_exists_hilbertSchmidt_factorization
    (T := ContinuousLinearMap.adjoint T)).mpr
  refine ⟨B, A, hB, hA, ?_⟩
  simpa only [star_mul, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint] using congrArg star hfactor

/-- Left composition by a bounded operator preserves trace-class membership. -/
theorem IsTraceClass.comp_left (W : H →L[ℂ] H) {T : H →L[ℂ] H}
    (hT : IsTraceClass T) :
    IsTraceClass (W * T) := by
  obtain ⟨A, B, hA, hB, hfactor⟩ :=
    (isTraceClass_iff_exists_hilbertSchmidt_factorization (T := T)).mp hT
  let A' : H →L[ℂ] H := A * ContinuousLinearMap.adjoint W
  have hA' : IsHilbertSchmidt A' :=
    isHilbertSchmidt_comp_right hA (ContinuousLinearMap.adjoint W)
  apply (isTraceClass_iff_exists_hilbertSchmidt_factorization (T := W * T)).mpr
  refine ⟨A', B, hA', hB, ?_⟩
  have hAdjA' : ContinuousLinearMap.adjoint A' = W * ContinuousLinearMap.adjoint A := by
    dsimp [A']
    simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star]
  rw [hAdjA', mul_assoc, hfactor]

/-- Right composition by a bounded operator preserves trace-class membership. -/
theorem IsTraceClass.comp_right {T : H →L[ℂ] H} (hT : IsTraceClass T)
    (W : H →L[ℂ] H) :
    IsTraceClass (T * W) := by
  simpa only [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star] using
    ((hT.adjoint.comp_left (ContinuousLinearMap.adjoint W)).adjoint)

/-- If `W` is a contraction, the absolute diagonal pairing with a trace-class operator is bounded
by the trace norm. -/
private theorem IsTraceClass.summable_norm_inner_left_and_tsum_le_traceNorm
    {T : H →L[ℂ] H} (hT : IsTraceClass T) (W : H →L[ℂ] H) (hW : ‖W‖ ≤ 1)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖inner ℂ (W (d i)) (T (d i))‖) ∧
      ∑' i, ‖inner ℂ (W (d i)) (T (d i))‖ ≤ hT.traceNorm := by
  obtain ⟨A, B, hA, hB, hfactor, hAnorm, hBnorm⟩ :=
    hT.exists_hilbertSchmidt_factorization_normSq_eq_traceNorm
  have hAW : IsHilbertSchmidt (A * W) := isHilbertSchmidt_comp_right hA W
  have hAWnorm : hAW.normSq ≤ hT.traceNorm := by
    calc
      hAW.normSq ≤ hA.normSq := hA.normSq_comp_right_le_of_norm_le_one W hW
      _ = hT.traceNorm := hAnorm
  have hpoint (x : H) :
      inner ℂ (W x) (T x) = inner ℂ ((A * W) x) (B x) := by
    rw [← hfactor, mul_apply_eq_comp, mul_apply_eq_comp]
    exact ContinuousLinearMap.adjoint_inner_right A (W x) (B x)
  simp_rw [hpoint]
  have hpair := hAW.summable_norm_inner_apply_and_tsum_le hB d
  refine ⟨hpair.1, hpair.2.trans ?_⟩
  calc
    Real.sqrt hAW.normSq * Real.sqrt hB.normSq ≤
        Real.sqrt hT.traceNorm * Real.sqrt hT.traceNorm := by
      rw [hBnorm]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hAWnorm) (Real.sqrt_nonneg _)
    _ = hT.traceNorm := by rw [← pow_two, Real.sq_sqrt hT.traceNorm_nonneg]

/-- Trace-class membership is closed under addition. -/
theorem IsTraceClass.add {T R : H →L[ℂ] H} (hT : IsTraceClass T) (hR : IsTraceClass R) :
    IsTraceClass (T + R) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  obtain ⟨U, -, hUright, hUnorm⟩ := exists_leftPolarFactor (T + R)
  have hTsum : Summable (fun i => inner ℂ (U (d i)) (T (d i))) :=
    Summable.of_norm (hT.summable_norm_inner_left_and_tsum_le_traceNorm U hUnorm d).1
  have hRsum : Summable (fun i => inner ℂ (U (d i)) (R (d i))) :=
    Summable.of_norm (hR.summable_norm_inner_left_and_tsum_le_traceNorm U hUnorm d).1
  have hsum :
      Summable (fun i => inner ℂ (U (d i)) ((T + R) (d i))) := by
    simpa [add_apply, inner_add_right] using hTsum.add hRsum
  have hcast :
      Summable (fun i =>
        (diagonalExpectationValue (CFC.abs (T + R))
          (CFC.abs_nonneg (T + R)).isSelfAdjoint (d i) : ℂ)) := by
    apply hsum.congr
    intro i
    symm
    rw [coe_diagonalExpectationValue_right, ← hUright, mul_apply_eq_comp]
    exact ContinuousLinearMap.adjoint_inner_right U (d i) ((T + R) (d i))
  apply (isTraceClass_iff_isTraceClassWrt d (T + R)).mpr
  rw [IsTraceClassWrt]
  exact Complex.summable_ofReal.mp hcast

namespace IsTraceClass

/-- The zero operator has trace zero. -/
@[simp]
theorem trace_zero :
    (isTraceClass_zero (H := H)).trace = 0 := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [(isTraceClass_zero (H := H)).trace_eq_tsum_inner d]
  simp

/-- The trace is complex-linear under scalar multiplication. -/
theorem trace_smul {T : H →L[ℂ] H} (hT : IsTraceClass T) (c : ℂ) :
    (hT.smul c).trace = c * hT.trace := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  apply ((hT.smul c).hasSum_trace d).unique
  simpa only [smul_apply, inner_smul_right] using (hT.hasSum_trace d).mul_left c

/-- The trace changes sign under negation. -/
@[simp]
theorem trace_neg {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    hT.neg.trace = -hT.trace := by
  simpa only [neg_one_smul, neg_one_mul] using hT.trace_smul (-1 : ℂ)

/-- The trace is additive. -/
theorem trace_add {T R : H →L[ℂ] H} (hT : IsTraceClass T) (hR : IsTraceClass R) :
    (hT.add hR).trace = hT.trace + hR.trace := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  apply ((hT.add hR).hasSum_trace d).unique
  simpa only [add_apply, inner_add_right] using (hT.hasSum_trace d).add (hR.hasSum_trace d)

/-- If `T` is trace class and `W` is bounded, then `Tr(TW) = Tr(WT)`. -/
theorem trace_comp_comm {T : H →L[ℂ] H} (hT : IsTraceClass T) (W : H →L[ℂ] H) :
    (hT.comp_right W).trace = (hT.comp_left W).trace := by
  obtain ⟨A, B, hA, hB, hfactor⟩ :=
    (isTraceClass_iff_exists_hilbertSchmidt_factorization (T := T)).mp hT
  obtain ⟨ι, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hfactorRight :
      ContinuousLinearMap.adjoint A * (B * W) = T * W := by
    rw [← mul_assoc, hfactor]
  have hAdjAW :
      ContinuousLinearMap.adjoint (A * ContinuousLinearMap.adjoint W) =
        W * ContinuousLinearMap.adjoint A := by
    simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star]
  have hfactorLeft :
      ContinuousLinearMap.adjoint (A * ContinuousLinearMap.adjoint W) * B = W * T := by
    rw [hAdjAW, mul_assoc, hfactor]
  calc
    (hT.comp_right W).trace = innerHS d A (B * W) :=
      trace_eq_innerHS_of_factorization (hT.comp_right W) hfactorRight d
    _ = innerHS d (A * ContinuousLinearMap.adjoint W) B :=
      innerHS_comp_right d hA hB W
    _ = (hT.comp_left W).trace :=
      (trace_eq_innerHS_of_factorization (hT.comp_left W) hfactorLeft d).symm

/-! ## Adjoint-conjugation closure and trace invariance -/

/-- Bounded adjoint conjugation preserves trace-class membership. -/
theorem adjointConjugate {T : H →L[ℂ] H} (hT : IsTraceClass T) (U : H →L[ℂ] H) :
    IsTraceClass (ContinuousLinearMap.adjointConjugate U T) := by
  simpa [ContinuousLinearMap.adjointConjugate, mul_assoc] using
    (hT.comp_left U).comp_right (star U)

/-- If `U† U = 1`, then `Tr(U T U†) = Tr(T)` for every trace-class `T`. -/
theorem trace_adjointConjugate {T : H →L[ℂ] H} (hT : IsTraceClass T) (U : H →L[ℂ] H)
    (hleft : star U * U = 1) :
    (hT.adjointConjugate U).trace = hT.trace := by
  simpa only [ContinuousLinearMap.adjointConjugate, ← mul_assoc, hleft, one_mul] using
    (hT.comp_left U).trace_comp_comm (star U)

end IsTraceClass


/-! ## Trace-norm operations -/

namespace IsTraceClass

/-- The zero operator has trace norm zero. -/
@[simp]
theorem traceNorm_zero :
    (isTraceClass_zero (H := H)).traceNorm = 0 := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [(isTraceClass_zero (H := H)).traceNorm_eq_tsum_diagonalExpectationValue d]
  simp_rw [CFC.abs_zero, diagonalExpectationValue_zero]
  simp

/-- Scalar multiplication scales the trace norm by the scalar norm. -/
theorem traceNorm_smul {T : H →L[ℂ] H} (hT : IsTraceClass T) (c : ℂ) :
    (hT.smul c).traceNorm = ‖c‖ * hT.traceNorm := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  apply ((hT.smul c).hasSum_abs_diagonalExpectationValue d).unique
  simpa only [diagonalExpectationValue_abs_smul] using
    (hT.hasSum_abs_diagonalExpectationValue d).mul_left ‖c‖

/-- Negation preserves the trace norm. -/
@[simp]
theorem traceNorm_neg {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    hT.neg.traceNorm = hT.traceNorm := by
  simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using
    hT.traceNorm_smul (-1 : ℂ)

private theorem traceNorm_adjoint_le {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    hT.adjoint.traceNorm ≤ hT.traceNorm := by
  obtain ⟨A, B, hA, hB, hfactor, hAnorm, hBnorm⟩ :=
    hT.exists_hilbertSchmidt_factorization_normSq_eq_traceNorm
  have hfactorAdj :
      ContinuousLinearMap.adjoint B * A = ContinuousLinearMap.adjoint T := by
    simpa only [star_mul, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint] using congrArg star hfactor
  have hbound :=
    hT.adjoint.traceNorm_le_sqrt_normSq_mul_of_factorization hB hA hfactorAdj
  calc
    hT.adjoint.traceNorm ≤ Real.sqrt hB.normSq * Real.sqrt hA.normSq := hbound
    _ = hT.traceNorm := by
      rw [hAnorm, hBnorm, ← pow_two, Real.sq_sqrt hT.traceNorm_nonneg]

/-- Taking the adjoint preserves the trace norm. -/
theorem traceNorm_adjoint {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    hT.adjoint.traceNorm = hT.traceNorm := by
  apply le_antisymm (traceNorm_adjoint_le hT)
  have hrev := traceNorm_adjoint_le hT.adjoint
  have hTT : IsTraceClass T := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hT.adjoint.adjoint
  have hrev' : hTT.traceNorm ≤ hT.adjoint.traceNorm := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hrev
  exact (hT.traceNorm_proof_irrel hTT).le.trans hrev'

/-- Left multiplication by a bounded operator scales the trace norm by at most its
operator norm. -/
theorem traceNorm_comp_left_le
    {T : H →L[ℂ] H} (hT : IsTraceClass T) (W : H →L[ℂ] H) :
    (hT.comp_left W).traceNorm ≤ ‖W‖ * hT.traceNorm := by
  obtain ⟨A, B, hA, hB, hfactor, hAnorm, hBnorm⟩ :=
    hT.exists_hilbertSchmidt_factorization_normSq_eq_traceNorm
  have hAW := isHilbertSchmidt_comp_right hA (ContinuousLinearMap.adjoint W)
  have hf : ContinuousLinearMap.adjoint (A * ContinuousLinearMap.adjoint W) * B = W * T := by
    have hadj : ContinuousLinearMap.adjoint (A * ContinuousLinearMap.adjoint W) =
        W * ContinuousLinearMap.adjoint A := by
      simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star]
    rw [hadj, mul_assoc, hfactor]
  have hbound : hAW.normSq ≤ ‖W‖ ^ 2 * hT.traceNorm := by
    have h := hA.normSq_comp_right_le (ContinuousLinearMap.adjoint W)
    rw [hAnorm, ← ContinuousLinearMap.star_eq_adjoint, norm_star] at h
    exact h
  calc
    (hT.comp_left W).traceNorm ≤ Real.sqrt hAW.normSq * Real.sqrt hB.normSq :=
      (hT.comp_left W).traceNorm_le_sqrt_normSq_mul_of_factorization hAW hB hf
    _ ≤ Real.sqrt (‖W‖ ^ 2 * hT.traceNorm) * Real.sqrt hT.traceNorm := by
      rw [hBnorm]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hbound) (Real.sqrt_nonneg _)
    _ = ‖W‖ * hT.traceNorm := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg W), mul_assoc,
        ← pow_two, Real.sq_sqrt hT.traceNorm_nonneg]

/-- Right multiplication by a bounded operator scales the trace norm by at most its
operator norm. -/
theorem traceNorm_comp_right_le
    {T : H →L[ℂ] H} (hT : IsTraceClass T) (W : H →L[ℂ] H) :
    (hT.comp_right W).traceNorm ≤ ‖W‖ * hT.traceNorm := by
  have hprodAdj :
      ContinuousLinearMap.adjoint (T * W) =
        ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint T := by
    simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul]
  have hleft :=
    hT.adjoint.traceNorm_comp_left_le (ContinuousLinearMap.adjoint W)
  calc
    (hT.comp_right W).traceNorm =
        (hT.comp_right W).adjoint.traceNorm :=
      (hT.comp_right W).traceNorm_adjoint.symm
    _ = (hT.adjoint.comp_left (ContinuousLinearMap.adjoint W)).traceNorm :=
      traceNorm_congr (hT.comp_right W).adjoint
        (hT.adjoint.comp_left (ContinuousLinearMap.adjoint W)) hprodAdj
    _ ≤ ‖ContinuousLinearMap.adjoint W‖ * hT.adjoint.traceNorm := hleft
    _ = ‖W‖ * hT.traceNorm := by
      rw [← ContinuousLinearMap.star_eq_adjoint, norm_star, hT.traceNorm_adjoint]

/-- The trace norm satisfies the triangle inequality. -/
theorem traceNorm_add_le {T R : H →L[ℂ] H} (hT : IsTraceClass T) (hR : IsTraceClass R) :
    (hT.add hR).traceNorm ≤ hT.traceNorm + hR.traceNorm := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  obtain ⟨U, -, hUright, hUnorm⟩ := exists_leftPolarFactor (T + R)
  have hTpair := hT.summable_norm_inner_left_and_tsum_le_traceNorm U hUnorm d
  have hRpair := hR.summable_norm_inner_left_and_tsum_le_traceNorm U hUnorm d
  have hsumPair :=
    (hT.add hR).summable_norm_inner_left_and_tsum_le_traceNorm U hUnorm d
  have hrhsSum := hTpair.1.add hRpair.1
  have hpoint_le (i : w) :
      ‖inner ℂ (U (d i)) ((T + R) (d i))‖ ≤
        ‖inner ℂ (U (d i)) (T (d i))‖ +
          ‖inner ℂ (U (d i)) (R (d i))‖ := by
    simpa [add_apply, inner_add_right] using
      norm_add_le (inner ℂ (U (d i)) (T (d i)))
        (inner ℂ (U (d i)) (R (d i)))
  rw [(hT.add hR).traceNorm_eq_tsum_norm_inner_left_of_polar U hUright d]
  calc
    (∑' i, ‖inner ℂ (U (d i)) ((T + R) (d i))‖) ≤
        ∑' i, (‖inner ℂ (U (d i)) (T (d i))‖ +
          ‖inner ℂ (U (d i)) (R (d i))‖) :=
      hsumPair.1.tsum_le_tsum hpoint_le hrhsSum
    _ = (∑' i, ‖inner ℂ (U (d i)) (T (d i))‖) +
        ∑' i, ‖inner ℂ (U (d i)) (R (d i))‖ :=
      hTpair.1.tsum_add hRpair.1
    _ ≤ hT.traceNorm + hR.traceNorm := add_le_add hTpair.2 hRpair.2

/-- The trace norm dominates the modulus of the trace. -/
theorem norm_trace_le_traceNorm {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    ‖hT.trace‖ ≤ hT.traceNorm := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hpair := hT.summable_norm_inner_left_and_tsum_le_traceNorm
    (ContinuousLinearMap.id ℂ H) ContinuousLinearMap.norm_id_le d
  rw [hT.trace_eq_tsum_inner d]
  exact (norm_tsum_le_tsum_norm (hT.summable_trace_diagonal d).norm).trans (by
    simpa using hpair.2)

end IsTraceClass

end ContinuousLinearMap
