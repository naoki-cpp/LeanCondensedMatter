import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Norm

set_option linter.style.header false

/-!
# Operations on general trace-class operators

Basic closure, trace-linearity, and trace-norm inequalities for the canonical general trace-class
API.
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

/-- The zero bounded operator is trace class. -/
theorem isTraceClass_zero : IsTraceClass (0 : H →L[ℂ] H) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  apply IsTraceClass.of_isTraceClassWrt (d := d)
  rw [IsTraceClassWrt]
  simpa only [CFC.abs_zero] using
    (summable_zero.congr fun i =>
      (diagonalExpectationValue_zero
        (show IsSelfAdjoint (0 : H →L[ℂ] H) by simp) (d i)).symm)

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

/-- Trace-class membership is closed under complex scalar multiplication. -/
theorem IsTraceClass.smul {T : H →L[ℂ] H} (hT : IsTraceClass T) (c : ℂ) :
    IsTraceClass (c • T) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  apply IsTraceClass.of_isTraceClassWrt (d := d)
  rw [IsTraceClassWrt]
  have hsum := hT.isTraceClassWrt d
  rw [IsTraceClassWrt] at hsum
  exact (hsum.mul_left ‖c‖).congr fun i => (diagonalExpectationValue_abs_smul c T (d i)).symm

/-- Trace-class membership is closed under negation. -/
theorem IsTraceClass.neg {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass (-T) := by
  simpa only [neg_one_smul] using hT.smul (-1 : ℂ)

/-- A product `A† B` of Hilbert--Schmidt operators is trace class. -/
theorem IsTraceClass.of_hilbertSchmidt_factorization
    {A B T : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B)
    (hfactor : ContinuousLinearMap.adjoint A * B = T) :
    IsTraceClass T := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  obtain ⟨U, -, hUright, -⟩ := exists_leftPolarFactor T
  have hAU : IsHilbertSchmidt (A * U) := isHilbertSchmidt_comp_right hA U
  have hsum := summable_inner_apply_of_isHilbertSchmidtWrt d
    (hAU.isHilbertSchmidtWrt d) (hB.isHilbertSchmidtWrt d)
  have hpoint (i : w) :
      ((diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i) : ℝ) : ℂ) =
        inner ℂ ((A * U) (d i)) (B (d i)) := by
    rw [coe_diagonalExpectationValue_right, ← hUright, mul_apply_eq_comp]
    calc
      inner ℂ (d i) ((ContinuousLinearMap.adjoint U) (T (d i))) =
          inner ℂ (U (d i)) (T (d i)) :=
        ContinuousLinearMap.adjoint_inner_right U (d i) (T (d i))
      _ = inner ℂ (U (d i)) ((ContinuousLinearMap.adjoint A * B) (d i)) := by
        rw [hfactor]
      _ = inner ℂ (U (d i)) ((ContinuousLinearMap.adjoint A) (B (d i))) := by
        rw [mul_apply_eq_comp]
      _ = inner ℂ (A (U (d i))) (B (d i)) :=
        ContinuousLinearMap.adjoint_inner_right A (U (d i)) (B (d i))
      _ = inner ℂ ((A * U) (d i)) (B (d i)) := by
        rw [mul_apply_eq_comp]
  have hcast :
      Summable (fun i =>
        ((diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i) : ℝ) : ℂ)) :=
    hsum.congr fun i => (hpoint i).symm
  apply IsTraceClass.of_isTraceClassWrt (d := d)
  rw [IsTraceClassWrt]
  exact Complex.summable_ofReal.mp hcast

/-- Taking the adjoint preserves trace-class membership. -/
theorem IsTraceClass.adjoint {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass (ContinuousLinearMap.adjoint T) := by
  obtain ⟨A, B, hA, hB, hfactor⟩ := hT.exists_hilbertSchmidt_factorization
  apply IsTraceClass.of_hilbertSchmidt_factorization hB hA
  simpa only [star_mul, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint] using congrArg star hfactor

/-- Left composition by a bounded operator preserves trace-class membership. -/
theorem IsTraceClass.comp_left (W : H →L[ℂ] H) {T : H →L[ℂ] H}
    (hT : IsTraceClass T) :
    IsTraceClass (W * T) := by
  obtain ⟨A, B, hA, hB, hfactor⟩ := hT.exists_hilbertSchmidt_factorization
  let A' : H →L[ℂ] H := A * ContinuousLinearMap.adjoint W
  have hA' : IsHilbertSchmidt A' :=
    isHilbertSchmidt_comp_right hA (ContinuousLinearMap.adjoint W)
  apply IsTraceClass.of_hilbertSchmidt_factorization hA' hB
  have hAdjA' : ContinuousLinearMap.adjoint A' = W * ContinuousLinearMap.adjoint A := by
    rw [show ContinuousLinearMap.adjoint A' = star A' from
      (ContinuousLinearMap.star_eq_adjoint A').symm]
    dsimp [A']
    rw [star_mul, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.star_eq_adjoint]
  rw [hAdjA', mul_assoc, hfactor]

/-- Right composition by a bounded operator preserves trace-class membership. -/
theorem IsTraceClass.comp_right {T : H →L[ℂ] H} (hT : IsTraceClass T)
    (W : H →L[ℂ] H) :
    IsTraceClass (T * W) := by
  obtain ⟨A, B, hA, hB, hfactor⟩ := hT.exists_hilbertSchmidt_factorization
  have hBW : IsHilbertSchmidt (B * W) := isHilbertSchmidt_comp_right hB W
  apply IsTraceClass.of_hilbertSchmidt_factorization hA hBW
  rw [← mul_assoc, hfactor]

/-- Pairing the image of a Hilbert basis by a bounded operator with a trace-class operator gives an
absolutely summable complex series. -/
theorem IsTraceClass.summable_inner_left {T : H →L[ℂ] H} (hT : IsTraceClass T)
    (W : H →L[ℂ] H) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    Summable (fun i => inner ℂ (W (d i)) (T (d i))) := by
  obtain ⟨A, B, hA, hB, hfactor⟩ := hT.exists_hilbertSchmidt_factorization
  have hAW : IsHilbertSchmidt (A * W) := isHilbertSchmidt_comp_right hA W
  have hsum := summable_inner_apply_of_isHilbertSchmidtWrt d
    (hAW.isHilbertSchmidtWrt d) (hB.isHilbertSchmidtWrt d)
  exact hsum.congr fun i => by
    calc
      inner ℂ ((A * W) (d i)) (B (d i)) =
          inner ℂ (W (d i)) ((ContinuousLinearMap.adjoint A) (B (d i))) :=
        (ContinuousLinearMap.adjoint_inner_right A (W (d i)) (B (d i))).symm
      _ = inner ℂ (W (d i)) (T (d i)) := by
        rw [← hfactor, mul_apply_eq_comp]

/-- If `W` is a contraction, the absolute diagonal pairing with a trace-class operator is bounded
by the trace norm. -/
theorem IsTraceClass.summable_norm_inner_left_and_tsum_le_traceNorm
    {T : H →L[ℂ] H} (hT : IsTraceClass T) (W : H →L[ℂ] H) (hW : ‖W‖ ≤ 1)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖inner ℂ (W (d i)) (T (d i))‖) ∧
      ∑' i, ‖inner ℂ (W (d i)) (T (d i))‖ ≤ hT.traceNorm := by
  obtain ⟨V, hVleft, -, hVnorm⟩ := exists_leftPolarFactor T
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  have hS : IsHilbertSchmidt S := hT
  have hSself : IsSelfAdjoint S := (CFC.sqrt_nonneg (CFC.abs T)).isSelfAdjoint
  have hSS : S * S = CFC.abs T :=
    CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
  let Bop : H →L[ℂ] H := ContinuousLinearMap.adjoint V * W
  have hBopNorm : ‖Bop‖ ≤ 1 := by
    calc
      ‖Bop‖ ≤ ‖ContinuousLinearMap.adjoint V‖ * ‖W‖ := norm_mul_le _ _
      _ = ‖V‖ * ‖W‖ := by rw [← ContinuousLinearMap.star_eq_adjoint, norm_star]
      _ ≤ 1 * ‖W‖ := mul_le_mul_of_nonneg_right hVnorm (norm_nonneg W)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hW zero_le_one
      _ = 1 := one_mul 1
  have hA : IsHilbertSchmidt (S * Bop) := isHilbertSchmidt_comp_right hS Bop
  have hSnorm : hS.normSq = hT.traceNorm := by
    unfold traceNorm
    exact IsHilbertSchmidt.normSq_proof_irrel hS
      (show IsHilbertSchmidt S from hT)
  have hAnorm_le : hA.normSq ≤ hT.traceNorm := by
    have hraw := IsHilbertSchmidt.normSq_comp_right_le hS Bop
    have hraw' : hA.normSq ≤ ‖Bop‖ ^ 2 * hS.normSq := by
      exact (IsHilbertSchmidt.normSq_proof_irrel hA
        (isHilbertSchmidt_comp_right hS Bop)) ▸ hraw
    calc
      hA.normSq ≤ ‖Bop‖ ^ 2 * hS.normSq := hraw'
      _ ≤ 1 ^ 2 * hS.normSq := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg Bop) hBopNorm 2) hS.normSq_nonneg
      _ = hT.traceNorm := by rw [one_pow, one_mul, hSnorm]
  have hfactor : V * (S * S) = T := by rw [hSS, hVleft]
  have hpoint (x : H) :
      inner ℂ (W x) (T x) = inner ℂ ((S * Bop) x) (S x) := by
    calc
      inner ℂ (W x) (T x) = inner ℂ (W x) ((V * (S * S)) x) := by rw [hfactor]
      _ = inner ℂ (W x) (V (S (S x))) := by simp [mul_apply_eq_comp]
      _ = inner ℂ ((ContinuousLinearMap.adjoint V) (W x)) (S (S x)) := by
        simpa using
          (ContinuousLinearMap.adjoint_inner_right (ContinuousLinearMap.adjoint V)
            (W x) (S (S x)))
      _ = inner ℂ (S ((ContinuousLinearMap.adjoint V) (W x))) (S x) := by
        simpa [hSself.adjoint_eq] using
          (ContinuousLinearMap.adjoint_inner_right S
            ((ContinuousLinearMap.adjoint V) (W x)) (S x))
      _ = inner ℂ ((S * Bop) x) (S x) := by
        simp [Bop, mul_apply_eq_comp]
  have hnormSummable :
      Summable (fun i => ‖inner ℂ (W (d i)) (T (d i))‖) := by
    have hpair := summable_inner_apply_of_isHilbertSchmidtWrt d
      (hA.isHilbertSchmidtWrt d) (hS.isHilbertSchmidtWrt d)
    exact (hpair.congr fun i => (hpoint (d i)).symm).norm
  have hAhas : HasSum (fun i => ‖(S * Bop) (d i)‖ ^ 2) hA.normSq := by
    rw [hA.normSq_eq_seriesWrt d]
    exact (hA.isHilbertSchmidtWrt d).hasSum
  have hShas : HasSum (fun i => ‖S (d i)‖ ^ 2) hS.normSq := by
    rw [hS.normSq_eq_seriesWrt d]
    exact (hS.isHilbertSchmidtWrt d).hasSum
  have hmajorHas :
      HasSum (fun i => (‖(S * Bop) (d i)‖ ^ 2 + ‖S (d i)‖ ^ 2) / 2)
        ((hA.normSq + hS.normSq) / 2) :=
    (hAhas.add hShas).div_const 2
  have hpoint_le (i : ι) :
      ‖inner ℂ (W (d i)) (T (d i))‖ ≤
        (‖(S * Bop) (d i)‖ ^ 2 + ‖S (d i)‖ ^ 2) / 2 := by
    rw [hpoint]
    exact (norm_inner_le_norm ((S * Bop) (d i)) (S (d i))).trans (by
      nlinarith [sq_nonneg (‖(S * Bop) (d i)‖ - ‖S (d i)‖)])
  have hsum_le :
      (∑' i, ‖inner ℂ (W (d i)) (T (d i))‖) ≤
        (hA.normSq + hS.normSq) / 2 :=
    (hnormSummable.tsum_le_tsum hpoint_le hmajorHas.summable).trans_eq hmajorHas.tsum_eq
  refine ⟨hnormSummable, hsum_le.trans ?_⟩
  rw [hSnorm]
  linarith

/-- Trace-class membership is closed under addition. -/
theorem IsTraceClass.add {T R : H →L[ℂ] H} (hT : IsTraceClass T) (hR : IsTraceClass R) :
    IsTraceClass (T + R) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  obtain ⟨U, -, hUright, -⟩ := exists_leftPolarFactor (T + R)
  have hTsum := hT.summable_inner_left U d
  have hRsum := hR.summable_inner_left U d
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
  apply IsTraceClass.of_isTraceClassWrt (d := d)
  rw [IsTraceClassWrt]
  exact Complex.summable_ofReal.mp hcast

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

/-- The trace norm satisfies the triangle inequality. -/
theorem traceNorm_add_le {T R : H →L[ℂ] H} (hT : IsTraceClass T) (hR : IsTraceClass R) :
    (hT.add hR).traceNorm ≤ hT.traceNorm + hR.traceNorm := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  obtain ⟨U, -, hUright, hUnorm⟩ := exists_leftPolarFactor (T + R)
  have hTpair := hT.summable_norm_inner_left_and_tsum_le_traceNorm U hUnorm d
  have hRpair := hR.summable_norm_inner_left_and_tsum_le_traceNorm U hUnorm d
  have hdiagCast (i : w) :
      (diagonalExpectationValue (CFC.abs (T + R))
        (CFC.abs_nonneg (T + R)).isSelfAdjoint (d i) : ℂ) =
        inner ℂ (U (d i)) ((T + R) (d i)) := by
    rw [coe_diagonalExpectationValue_right, ← hUright, mul_apply_eq_comp]
    exact ContinuousLinearMap.adjoint_inner_right U (d i) ((T + R) (d i))
  have hdiagNorm (i : w) :
      diagonalExpectationValue (CFC.abs (T + R))
        (CFC.abs_nonneg (T + R)).isSelfAdjoint (d i) =
        ‖inner ℂ (U (d i)) ((T + R) (d i))‖ := by
    have hnonneg := diagonalExpectationValue_nonneg
      (CFC.abs (T + R)) (nonneg_iff_isPositive.mp (CFC.abs_nonneg (T + R))) (d i)
    have hnorm := congrArg norm (hdiagCast i)
    have hcastNorm :
        ‖(diagonalExpectationValue (CFC.abs (T + R))
          (CFC.abs_nonneg (T + R)).isSelfAdjoint (d i) : ℂ)‖ =
          diagonalExpectationValue (CFC.abs (T + R))
            (CFC.abs_nonneg (T + R)).isSelfAdjoint (d i) := by
      rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
    exact hcastNorm.symm.trans hnorm
  have hpoint_le (i : w) :
      diagonalExpectationValue (CFC.abs (T + R))
          (CFC.abs_nonneg (T + R)).isSelfAdjoint (d i) ≤
        ‖inner ℂ (U (d i)) (T (d i))‖ +
          ‖inner ℂ (U (d i)) (R (d i))‖ := by
    rw [hdiagNorm]
    simpa [add_apply, inner_add_right] using
      norm_add_le (inner ℂ (U (d i)) (T (d i)))
        (inner ℂ (U (d i)) (R (d i)))
  have hdiagSum := (hT.add hR).isTraceClassWrt d
  rw [IsTraceClassWrt] at hdiagSum
  have hrhsSum := hTpair.1.add hRpair.1
  rw [(hT.add hR).traceNorm_eq_tsum_diagonalExpectationValue d]
  calc
    (∑' i, diagonalExpectationValue (CFC.abs (T + R))
        (CFC.abs_nonneg (T + R)).isSelfAdjoint (d i)) ≤
        ∑' i, (‖inner ℂ (U (d i)) (T (d i))‖ +
          ‖inner ℂ (U (d i)) (R (d i))‖) :=
      hdiagSum.tsum_le_tsum hpoint_le hrhsSum
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
  rw [hT.trace_eq_seriesWrt d]
  unfold traceSeriesWrt
  exact (norm_tsum_le_tsum_norm (hT.summable_norm_traceSeriesWrt d)).trans (by
    simpa using hpair.2)

/-- The zero operator has trace zero. -/
@[simp]
theorem trace_zero :
    (isTraceClass_zero (H := H)).trace = 0 := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [(isTraceClass_zero (H := H)).trace_eq_seriesWrt d]
  simp [traceSeriesWrt]

/-- The trace is complex-linear under scalar multiplication. -/
theorem trace_smul {T : H →L[ℂ] H} (hT : IsTraceClass T) (c : ℂ) :
    (hT.smul c).trace = c * hT.trace := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [(hT.smul c).trace_eq_seriesWrt d, hT.trace_eq_seriesWrt d]
  unfold traceSeriesWrt
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  simp [inner_smul_right]

/-- The trace changes sign under negation. -/
@[simp]
theorem trace_neg {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    hT.neg.trace = -hT.trace := by
  simpa only [neg_one_smul, neg_one_mul] using hT.trace_smul (-1 : ℂ)

/-- The trace is additive. -/
theorem trace_add {T R : H →L[ℂ] H} (hT : IsTraceClass T) (hR : IsTraceClass R) :
    (hT.add hR).trace = hT.trace + hR.trace := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [(hT.add hR).trace_eq_seriesWrt d, hT.trace_eq_seriesWrt d, hR.trace_eq_seriesWrt d]
  unfold traceSeriesWrt
  simpa [add_apply, inner_add_right] using
    ((hT.summable_traceSeriesWrt d).hasSum.add
      (hR.summable_traceSeriesWrt d).hasSum).tsum_eq

end IsTraceClass

end ContinuousLinearMap
