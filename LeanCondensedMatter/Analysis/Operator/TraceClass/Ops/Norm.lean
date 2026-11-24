import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops.Basic
import LeanCondensedMatter.Analysis.Operator.TraceClass.General

set_option linter.style.header false

/-!
# Trace-norm operations on general trace-class operators

This module owns trace-norm behavior under scalar multiplication, adjoint, addition, and bounded
left/right composition, together with the bound of the complex trace by the trace norm.
It also owns the sharp Hilbert--Schmidt factorization bounds used to prove these trace-norm laws.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-! ## Trace-norm bounds for Hilbert--Schmidt factorizations -/

namespace IsTraceClass

/-- For any Hilbert--Schmidt factorization `T = A† B`, the trace norm is bounded by the arithmetic
mean of the squared Hilbert--Schmidt norms. -/
theorem traceNorm_le_half_normSq_add_of_factorization
    {T A B : H →L[ℂ] H} (hT : IsTraceClass T)
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B)
    (hfactor : ContinuousLinearMap.adjoint A * B = T) :
    hT.traceNorm ≤ (hA.normSq + hB.normSq) / 2 := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  obtain ⟨U, -, hUright, hUnorm⟩ := exists_leftPolarFactor T
  have hAU : IsHilbertSchmidt (A * U) := isHilbertSchmidt_comp_right hA U
  have hAUnorm_le : hAU.normSq ≤ hA.normSq :=
    hA.normSq_comp_right_le_of_norm_le_one U hUnorm
  have hterm (i : w) :
      inner ℂ (U (d i)) (T (d i)) =
        inner ℂ ((A * U) (d i)) (B (d i)) := by
    rw [← hfactor, mul_apply_eq_comp, mul_apply_eq_comp]
    exact ContinuousLinearMap.adjoint_inner_right A (U (d i)) (B (d i))
  have hpair := hAU.summable_norm_inner_apply_and_tsum_le hB d
  rw [hT.traceNorm_eq_tsum_norm_inner_left_of_polar U hUright d]
  calc
    (∑' i, ‖inner ℂ (U (d i)) (T (d i))‖) =
        ∑' i, ‖inner ℂ ((A * U) (d i)) (B (d i))‖ := by
      apply tsum_congr
      intro i
      rw [hterm]
    _ ≤ (hAU.normSq + hB.normSq) / 2 := hpair.2
    _ ≤ (hA.normSq + hB.normSq) / 2 := by linarith

/-- Every trace-class operator admits a Hilbert--Schmidt factorization whose two squared
Hilbert--Schmidt norms equal the trace norm. -/
theorem exists_hilbertSchmidt_factorization_normSq_eq_traceNorm
    {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    ∃ A B : H →L[ℂ] H, ∃ hA : IsHilbertSchmidt A, ∃ hB : IsHilbertSchmidt B,
      ContinuousLinearMap.adjoint A * B = T ∧
      hA.normSq = hT.traceNorm ∧ hB.normSq = hT.traceNorm := by
  obtain ⟨A, B, hA, hB, hfactor, hAnorm_le, hBnorm_le⟩ :=
    hT.exists_controlled_hilbertSchmidt_factorization
  have hAnorm_le' : hA.normSq ≤ hT.traceNorm := hAnorm_le
  have hBnorm_le' : hB.normSq ≤ hT.traceNorm := hBnorm_le
  have hlower := hT.traceNorm_le_half_normSq_add_of_factorization hA hB hfactor
  have hAnorm : hA.normSq = hT.traceNorm := by linarith
  have hBnorm : hB.normSq = hT.traceNorm := by linarith
  exact ⟨A, B, hA, hB, hfactor, hAnorm, hBnorm⟩

end IsTraceClass

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
  have hpair := hAW.summable_norm_inner_apply_and_tsum_le hB d
  have hnormSummable :
      Summable (fun i => ‖inner ℂ (W (d i)) (T (d i))‖) :=
    hpair.1.congr fun i => (congrArg norm (hpoint (d i))).symm
  have hsum_le :
      (∑' i, ‖inner ℂ (W (d i)) (T (d i))‖) ≤
        (hAW.normSq + hB.normSq) / 2 := by
    calc
      (∑' i, ‖inner ℂ (W (d i)) (T (d i))‖) =
          ∑' i, ‖inner ℂ ((A * W) (d i)) (B (d i))‖ :=
        tsum_congr fun i => congrArg norm (hpoint (d i))
      _ ≤ (hAW.normSq + hB.normSq) / 2 := hpair.2
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
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  obtain ⟨U, -, hUright, hUnorm⟩ := exists_leftPolarFactor (W * T)
  have hAdjWnorm : ‖ContinuousLinearMap.adjoint W‖ ≤ 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, norm_star]
    exact hW
  have hcontract : ‖ContinuousLinearMap.adjoint W * U‖ ≤ 1 := by
    calc
      ‖ContinuousLinearMap.adjoint W * U‖ ≤
          ‖ContinuousLinearMap.adjoint W‖ * ‖U‖ := norm_mul_le _ _
      _ ≤ 1 := by
        nlinarith [norm_nonneg (ContinuousLinearMap.adjoint W), norm_nonneg U]
  have hpair := hT.summable_norm_inner_left_and_tsum_le_traceNorm
    (ContinuousLinearMap.adjoint W * U) hcontract d
  rw [(hT.comp_left W).traceNorm_eq_tsum_norm_inner_left_of_polar U hUright d]
  calc
    (∑' i, ‖inner ℂ (U (d i)) ((W * T) (d i))‖) =
        ∑' i, ‖inner ℂ ((ContinuousLinearMap.adjoint W * U) (d i)) (T (d i))‖ := by
      apply tsum_congr
      intro i
      apply congrArg norm
      simpa only [mul_apply_eq_comp, ContinuousLinearMap.adjoint_adjoint] using
        (ContinuousLinearMap.adjoint_inner_right
          (ContinuousLinearMap.adjoint W) (U (d i)) (T (d i)))
    _ ≤ hT.traceNorm := hpair.2

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
      traceNorm_congr (hT.comp_left (0 : H →L[ℂ] H))
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
        traceNorm_congr (hT.comp_left W)
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
