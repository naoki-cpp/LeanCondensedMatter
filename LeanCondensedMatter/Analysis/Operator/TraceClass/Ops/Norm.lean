import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops.Basic
import LeanCondensedMatter.Analysis.Operator.TraceClass.Norm
import LeanCondensedMatter.Analysis.Operator.TraceClass.Factorization.Norm

set_option linter.style.header false

/-!
# Trace-norm operations on general trace-class operators

This module owns trace-norm behavior under scalar multiplication, adjoint, addition, and bounded
left/right composition, together with the bound of the complex trace by the trace norm.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem diagonalExpectationValue_zero
    (h0 : IsSelfAdjoint (0 : H →L[ℂ] H)) (x : H) :
    diagonalExpectationValue 0 h0 x = 0 := by
  apply Complex.ofReal_injective
  rw [coe_diagonalExpectationValue_right]
  simp

private theorem diagonalExpectationValue_abs_smul
    (c : ℂ) (T : H →L[ℂ] H) (x : H) :
    diagonalExpectationValue (CFC.abs (c • T)) (CFC.abs_nonneg (c • T)).isSelfAdjoint x =
      ‖c‖ * diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint x := by
  apply Complex.ofReal_injective
  rw [coe_diagonalExpectationValue_right, Complex.ofReal_mul,
    coe_diagonalExpectationValue_right, CFC.abs_smul]
  rw [smul_apply]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) ‖c‖ ((CFC.abs T) x)]
  rw [inner_smul_right]
  rfl

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
    have hraw := IsHilbertSchmidt.normSq_comp_right_le hA W
    have hraw' : hAW.normSq ≤ ‖W‖ ^ 2 * hA.normSq := by
      exact (IsHilbertSchmidt.normSq_proof_irrel hAW
        (isHilbertSchmidt_comp_right hA W)) ▸ hraw
    calc
      hAW.normSq ≤ ‖W‖ ^ 2 * hA.normSq := hraw'
      _ ≤ 1 ^ 2 * hA.normSq := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg W) hW 2) hA.normSq_nonneg
      _ = hA.normSq := by rw [one_pow, one_mul]
      _ = hT.traceNorm := hAnorm
  have hpoint (x : H) :
      inner ℂ (W x) (T x) = inner ℂ ((A * W) x) (B x) := by
    calc
      inner ℂ (W x) (T x) =
          inner ℂ (W x) ((ContinuousLinearMap.adjoint A * B) x) := by rw [hfactor]
      _ = inner ℂ (W x) ((ContinuousLinearMap.adjoint A) (B x)) := by
        rw [mul_apply_eq_comp]
      _ = inner ℂ (A (W x)) (B x) :=
        ContinuousLinearMap.adjoint_inner_right A (W x) (B x)
      _ = inner ℂ ((A * W) x) (B x) := by rw [mul_apply_eq_comp]
  have hnormSummable :
      Summable (fun i => ‖inner ℂ (W (d i)) (T (d i))‖) := by
    have hpair := hAW.summable_inner_apply hB d
    exact (hpair.congr fun i => (hpoint (d i)).symm).norm
  have hAWhas : HasSum (fun i => ‖(A * W) (d i)‖ ^ 2) hAW.normSq :=
    hAW.hasSum_norm_sq_apply d
  have hBhas : HasSum (fun i => ‖B (d i)‖ ^ 2) hB.normSq :=
    hB.hasSum_norm_sq_apply d
  have hmajorHas :
      HasSum (fun i => (‖(A * W) (d i)‖ ^ 2 + ‖B (d i)‖ ^ 2) / 2)
        ((hAW.normSq + hB.normSq) / 2) :=
    (hAWhas.add hBhas).div_const 2
  have hpoint_le (i : ι) :
      ‖inner ℂ (W (d i)) (T (d i))‖ ≤
        (‖(A * W) (d i)‖ ^ 2 + ‖B (d i)‖ ^ 2) / 2 := by
    rw [hpoint]
    exact (norm_inner_le_norm ((A * W) (d i)) (B (d i))).trans (by
      nlinarith [sq_nonneg (‖(A * W) (d i)‖ - ‖B (d i)‖)])
  have hsum_le :
      (∑' i, ‖inner ℂ (W (d i)) (T (d i))‖) ≤
        (hAW.normSq + hB.normSq) / 2 :=
    (hnormSummable.tsum_le_tsum hpoint_le hmajorHas.summable).trans_eq hmajorHas.tsum_eq
  refine ⟨hnormSummable, hsum_le.trans ?_⟩
  linarith

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
  rw [(hT.smul c).traceNorm_eq_tsum_diagonalExpectationValue d,
    hT.traceNorm_eq_tsum_diagonalExpectationValue d]
  simp_rw [diagonalExpectationValue_abs_smul c T]
  rw [tsum_mul_left]

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
    hT.adjoint.traceNorm_le_half_normSq_add_of_factorization hB hA hfactorAdj
  calc
    hT.adjoint.traceNorm ≤ (hB.normSq + hA.normSq) / 2 := hbound
    _ = hT.traceNorm := by rw [hAnorm, hBnorm]; ring

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
/-- Left multiplication by a contraction does not increase the trace norm. -/
private theorem traceNorm_comp_left_le_of_norm_le_one
    {T : H →L[ℂ] H} (hT : IsTraceClass T) (W : H →L[ℂ] H) (hW : ‖W‖ ≤ 1) :
    (hT.comp_left W).traceNorm ≤ hT.traceNorm := by
  obtain ⟨A, B, hA, hB, hfactor, hAnorm, hBnorm⟩ :=
    hT.exists_hilbertSchmidt_factorization_normSq_eq_traceNorm
  let A' : H →L[ℂ] H := A * ContinuousLinearMap.adjoint W
  have hA' : IsHilbertSchmidt A' :=
    isHilbertSchmidt_comp_right hA (ContinuousLinearMap.adjoint W)
  have hAdjA' : ContinuousLinearMap.adjoint A' = W * ContinuousLinearMap.adjoint A := by
    rw [show ContinuousLinearMap.adjoint A' = star A' from
      (ContinuousLinearMap.star_eq_adjoint A').symm]
    dsimp [A']
    rw [star_mul, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.star_eq_adjoint]
  have hfactor' : ContinuousLinearMap.adjoint A' * B = W * T := by
    rw [hAdjA', mul_assoc, hfactor]
  have hAdjWnorm : ‖ContinuousLinearMap.adjoint W‖ ≤ 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, norm_star]
    exact hW
  have hA'norm : hA'.normSq ≤ hT.traceNorm := by
    have hraw := IsHilbertSchmidt.normSq_comp_right_le hA (ContinuousLinearMap.adjoint W)
    have hraw' : hA'.normSq ≤ ‖ContinuousLinearMap.adjoint W‖ ^ 2 * hA.normSq := by
      exact (IsHilbertSchmidt.normSq_proof_irrel hA'
        (isHilbertSchmidt_comp_right hA (ContinuousLinearMap.adjoint W))) ▸ hraw
    calc
      hA'.normSq ≤ ‖ContinuousLinearMap.adjoint W‖ ^ 2 * hA.normSq := hraw'
      _ ≤ 1 ^ 2 * hA.normSq := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hAdjWnorm 2) hA.normSq_nonneg
      _ = hT.traceNorm := by rw [one_pow, one_mul, hAnorm]
  have hbound :=
    (hT.comp_left W).traceNorm_le_half_normSq_add_of_factorization hA' hB hfactor'
  calc
    (hT.comp_left W).traceNorm ≤ (hA'.normSq + hB.normSq) / 2 := hbound
    _ ≤ hT.traceNorm := by rw [hBnorm]; linarith

private theorem traceNorm_eq_of_eq
    {S R : H →L[ℂ] H} (hS : IsTraceClass S) (hR : IsTraceClass R) (hSR : S = R) :
    hS.traceNorm = hR.traceNorm := by
  subst R
  exact IsTraceClass.traceNorm_proof_irrel _ _

/-- Left multiplication by a bounded operator scales the trace norm by at most its
operator norm. -/
theorem traceNorm_comp_left_le
    {T : H →L[ℂ] H} (hT : IsTraceClass T) (W : H →L[ℂ] H) :
    (hT.comp_left W).traceNorm ≤ ‖W‖ * hT.traceNorm := by
  by_cases hWzero : W = 0
  · subst W
    have hzero :
        (hT.comp_left (0 : H →L[ℂ] H)).traceNorm =
          (isTraceClass_zero (H := H)).traceNorm :=
      traceNorm_eq_of_eq (hT.comp_left (0 : H →L[ℂ] H))
        (isTraceClass_zero (H := H)) (by simp)
    rw [hzero, traceNorm_zero]
    simp
  · have hWpos : 0 < ‖W‖ := norm_pos_iff.mpr hWzero
    let W₀ : H →L[ℂ] H := ((‖W‖ : ℂ)⁻¹) • W
    have hW₀norm : ‖W₀‖ = 1 := by
      simp [W₀, norm_smul, norm_inv, hWpos.ne']
    have hcontract :
        (hT.comp_left W₀).traceNorm ≤ hT.traceNorm :=
      traceNorm_comp_left_le_of_norm_le_one hT W₀ hW₀norm.le
    have hscale : (‖W‖ : ℂ) • W₀ = W := by
      simp [W₀, smul_smul, hWpos.ne']
    have hprod :
        W * T = (‖W‖ : ℂ) • (W₀ * T) := by
      calc
        W * T = ((‖W‖ : ℂ) • W₀) * T := by rw [hscale]
        _ = (‖W‖ : ℂ) • (W₀ * T) := by rw [smul_mul_assoc]
    calc
      (hT.comp_left W).traceNorm =
          ((hT.comp_left W₀).smul (‖W‖ : ℂ)).traceNorm :=
        traceNorm_eq_of_eq (hT.comp_left W)
          ((hT.comp_left W₀).smul (‖W‖ : ℂ)) hprod
      _ = ‖(‖W‖ : ℂ)‖ * (hT.comp_left W₀).traceNorm :=
        (hT.comp_left W₀).traceNorm_smul (‖W‖ : ℂ)
      _ ≤ ‖(‖W‖ : ℂ)‖ * hT.traceNorm :=
        mul_le_mul_of_nonneg_left hcontract (norm_nonneg (‖W‖ : ℂ))
      _ = ‖W‖ * hT.traceNorm := by simp

/-- Right multiplication by a bounded operator scales the trace norm by at most its
operator norm. -/
theorem traceNorm_comp_right_le
    {T : H →L[ℂ] H} (hT : IsTraceClass T) (W : H →L[ℂ] H) :
    (hT.comp_right W).traceNorm ≤ ‖W‖ * hT.traceNorm := by
  have hprodAdj :
      ContinuousLinearMap.adjoint (T * W) =
        ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint T := by
    rw [show ContinuousLinearMap.adjoint (T * W) = star (T * W) from
      (ContinuousLinearMap.star_eq_adjoint (T * W)).symm]
    rw [star_mul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint]
  have hleft :=
    hT.adjoint.traceNorm_comp_left_le (ContinuousLinearMap.adjoint W)
  calc
    (hT.comp_right W).traceNorm =
        (hT.comp_right W).adjoint.traceNorm :=
      (hT.comp_right W).traceNorm_adjoint.symm
    _ = (hT.adjoint.comp_left (ContinuousLinearMap.adjoint W)).traceNorm :=
      traceNorm_eq_of_eq (hT.comp_right W).adjoint
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
