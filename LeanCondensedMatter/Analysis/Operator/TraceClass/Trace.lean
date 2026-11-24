import LeanCondensedMatter.Analysis.Operator.TraceClass.General
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Norm
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Compact
import LeanCondensedMatter.Analysis.Operator.Polar
import Mathlib.Analysis.InnerProductSpace.Trace

set_option linter.style.header false

/-!
# Factorization and trace of general trace-class operators

A bounded operator is trace class exactly when it factors as `A† B` with Hilbert--Schmidt
factors. The sharp factorization attains the trace norm and yields compactness. The canonical
complex trace is the basis-independent diagonal sum; factorization supplies absolute convergence
and basis independence. The real trace and finite-dimensional trace formulas are derived here.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

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
  obtain ⟨U, hUleft, -, hUnorm⟩ := exists_leftPolarFactor T
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  have hS : IsHilbertSchmidt S := hT
  have hSself : IsSelfAdjoint S := (CFC.sqrt_nonneg (CFC.abs T)).isSelfAdjoint
  have hSS : S * S = CFC.abs T :=
    CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
  let A : H →L[ℂ] H := S * ContinuousLinearMap.adjoint U
  have hA : IsHilbertSchmidt A :=
    isHilbertSchmidt_comp_right hS (ContinuousLinearMap.adjoint U)
  have hAdjA : ContinuousLinearMap.adjoint A = U * S := by
    simpa only [A, ← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star,
      (ContinuousLinearMap.star_eq_adjoint S).trans hSself.adjoint_eq]
  have hfactor : ContinuousLinearMap.adjoint A * S = T := by
    rw [hAdjA, mul_assoc, hSS, hUleft]
  have hSnorm : hS.normSq = hT.traceNorm := rfl
  have hAdjUnorm : ‖ContinuousLinearMap.adjoint U‖ ≤ 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, norm_star]
    exact hUnorm
  have hAnorm_le : hA.normSq ≤ hT.traceNorm := by
    calc
      hA.normSq ≤ hS.normSq :=
        hS.normSq_comp_right_le_of_norm_le_one (ContinuousLinearMap.adjoint U) hAdjUnorm
      _ = hT.traceNorm := hSnorm
  have hlower := hT.traceNorm_le_half_normSq_add_of_factorization hA hS hfactor
  have hAnorm : hA.normSq = hT.traceNorm := by linarith
  exact ⟨A, S, hA, hS, hfactor, hAnorm, hSnorm⟩

end IsTraceClass

/-- A bounded operator is trace class exactly when it admits a factorization `A† B` with
Hilbert--Schmidt factors. -/
theorem isTraceClass_iff_exists_hilbertSchmidt_factorization {T : H →L[ℂ] H} :
    IsTraceClass T ↔
      ∃ A B : H →L[ℂ] H,
        IsHilbertSchmidt A ∧ IsHilbertSchmidt B ∧ ContinuousLinearMap.adjoint A * B = T := by
  constructor
  · intro hT
    obtain ⟨A, B, hA, hB, hfactor, -, -⟩ :=
      hT.exists_hilbertSchmidt_factorization_normSq_eq_traceNorm
    exact ⟨A, B, hA, hB, hfactor⟩
  · rintro ⟨A, B, hA, hB, hfactor⟩
    obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
    obtain ⟨U, -, hUright, -⟩ := exists_leftPolarFactor T
    have hAU : IsHilbertSchmidt (A * U) := isHilbertSchmidt_comp_right hA U
    have hsum := hAU.summable_inner_apply hB d
    have hpoint (i : w) :
        ((diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i) : ℝ) : ℂ) =
          inner ℂ ((A * U) (d i)) (B (d i)) := by
      rw [coe_diagonalExpectationValue_right, ← hUright, mul_apply_eq_comp,
        ContinuousLinearMap.adjoint_inner_right U (d i) (T (d i))]
      rw [← hfactor, mul_apply_eq_comp, mul_apply_eq_comp]
      exact ContinuousLinearMap.adjoint_inner_right A (U (d i)) (B (d i))
    have hcast :
        Summable (fun i =>
          ((diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i) : ℝ) : ℂ)) :=
      hsum.congr fun i => (hpoint i).symm
    apply (isTraceClass_iff_isTraceClassWrt d T).mpr
    rw [IsTraceClassWrt]
    exact Complex.summable_ofReal.mp hcast

namespace IsTraceClass

/-- Every trace-class operator is compact. -/
theorem isCompact {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsCompactOperator T := by
  obtain ⟨A, B, -, hB, hfactor⟩ :=
    (isTraceClass_iff_exists_hilbertSchmidt_factorization (T := T)).mp hT
  rw [← hfactor]
  change IsCompactOperator
    (⇑(ContinuousLinearMap.adjoint A) ∘ ⇑B)
  exact hB.isCompact.clm_comp (ContinuousLinearMap.adjoint A)


end IsTraceClass

/-! ## Basis-independent trace -/

private theorem diagonal_eq_hilbertSchmidt_inner
    {T A B : H →L[ℂ] H} (hfactor : ContinuousLinearMap.adjoint A * B = T)
    (x : H) :
    inner ℂ x (T x) = inner ℂ (A x) (B x) := by
  rw [← hfactor, mul_apply_eq_comp]
  exact ContinuousLinearMap.adjoint_inner_right A x (B x)

/-- The complex diagonal series of a trace-class operator is absolutely summable in every Hilbert
basis. -/
theorem IsTraceClass.summable_trace_diagonal {T : H →L[ℂ] H}
    (hT : IsTraceClass T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    Summable (fun i => inner ℂ (d i) (T (d i))) := by
  obtain ⟨A, B, hA, hB, hfactor⟩ :=
    (isTraceClass_iff_exists_hilbertSchmidt_factorization (T := T)).mp hT
  have hsum := hA.summable_inner_apply hB d
  exact hsum.congr fun i => (diagonal_eq_hilbertSchmidt_inner hfactor (d i)).symm

/-- The diagonal `tsum` of a trace-class operator is independent of the Hilbert basis. -/
private theorem trace_tsum_eq {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    (∑' i, inner ℂ (d i) (T (d i))) = ∑' j, inner ℂ (f j) (T (f j)) := by
  obtain ⟨A, B, hA, hB, hfactor⟩ :=
    (isTraceClass_iff_exists_hilbertSchmidt_factorization (T := T)).mp hT
  have hd : (∑' i, inner ℂ (d i) (T (d i))) = innerHS d A B := by
    unfold innerHS
    apply tsum_congr
    intro i
    exact diagonal_eq_hilbertSchmidt_inner hfactor (d i)
  have hf : (∑' j, inner ℂ (f j) (T (f j))) = innerHS f A B := by
    unfold innerHS
    apply tsum_congr
    intro j
    exact diagonal_eq_hilbertSchmidt_inner hfactor (f j)
  rw [hd, hf]
  exact innerHS_eq_of_isHilbertSchmidt d f hA hB

namespace IsTraceClass

/-- The basis-independent complex trace of a trace-class operator. -/
noncomputable def trace {T : H →L[ℂ] H} (hT : IsTraceClass T) : ℂ :=
  let w : Set H := Classical.choose hT
  let hw : ∃ d : HilbertBasis w ℂ H,
      IsHilbertSchmidtWrt d (CFC.sqrt (CFC.abs T)) := Classical.choose_spec hT
  let d : HilbertBasis w ℂ H := Classical.choose hw
  ∑' i, inner ℂ (d i) (T (d i))

/-- The trace is the diagonal `tsum` in every Hilbert basis. -/
theorem trace_eq_tsum_inner {T : H →L[ℂ] H} (hT : IsTraceClass T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.trace = ∑' i, inner ℂ (d i) (T (d i)) := by
  unfold trace
  exact trace_tsum_eq _ d T hT

/-- The trace of a rank-one operator is the inner product of its defining vectors. -/
theorem trace_rankOne {x y : H}
    (hT : IsTraceClass (InnerProductSpace.rankOne ℂ x y)) :
    hT.trace = inner ℂ y x := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [hT.trace_eq_tsum_inner d]
  simpa only [InnerProductSpace.rankOne_apply, inner_smul_right] using
    d.tsum_inner_mul_inner y x

/-- The trace of a Hilbert--Schmidt factorization `T = A† B` is the
Hilbert--Schmidt inner product of its factors in any Hilbert basis. -/
theorem trace_eq_innerHS_of_factorization
    {T A B : H →L[ℂ] H} (hT : IsTraceClass T)
    (hfactor : ContinuousLinearMap.adjoint A * B = T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.trace = innerHS d A B := by
  rw [hT.trace_eq_tsum_inner d]
  unfold innerHS
  exact tsum_congr fun i => diagonal_eq_hilbertSchmidt_inner hfactor (d i)

/-- The canonical trace depends only on the underlying operator, not on the supplied
trace-class witnesses. -/
theorem trace_congr {T R : H →L[ℂ] H}
    (hT : IsTraceClass T) (hR : IsTraceClass R) (h : T = R) :
    hT.trace = hR.trace := by
  subst R
  exact congrArg (fun p : IsTraceClass T => p.trace) (Subsingleton.elim hT hR)

/-- The diagonal series sums to the trace in every Hilbert basis. -/
theorem hasSum_trace {T : H →L[ℂ] H} (hT : IsTraceClass T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => inner ℂ (d i) (T (d i))) hT.trace := by
  rw [hT.trace_eq_tsum_inner d]
  exact (hT.summable_trace_diagonal d).hasSum

/-- The trace of a self-adjoint trace-class operator has zero imaginary part. -/
theorem trace_im_eq_zero_of_isSelfAdjoint {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (hself : IsSelfAdjoint T) :
    hT.trace.im = 0 := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [hT.trace_eq_tsum_inner d, Complex.im_tsum (hT.summable_trace_diagonal d)]
  calc
    (∑' i, (inner ℂ (d i) (T (d i)) : ℂ).im) =
        ∑' _i, (0 : ℝ) := by
      apply tsum_congr
      intro i
      exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself).im_inner_self_apply (d i)
    _ = 0 := tsum_zero

/-- The trace of a self-adjoint trace-class operator, bundled as a self-adjoint complex scalar. -/
noncomputable def traceSelfAdjoint {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (hself : IsSelfAdjoint T) : selfAdjoint ℂ :=
  ⟨hT.trace,
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mp
      (hT.trace_im_eq_zero_of_isSelfAdjoint hself)⟩

/-- The lossless real trace of a self-adjoint trace-class operator. -/
noncomputable def realTrace {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (hself : IsSelfAdjoint T) : ℝ :=
  Complex.selfAdjointEquiv (hT.traceSelfAdjoint hself)

/-- Coercing the lossless real trace back to `ℂ` recovers the canonical complex trace. -/
@[simp]
theorem coe_realTrace {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (hself : IsSelfAdjoint T) :
    (hT.realTrace hself : ℂ) = hT.trace := by
  simpa [realTrace, traceSelfAdjoint] using
    Complex.coe_selfAdjointEquiv (hT.traceSelfAdjoint hself)

/-- The lossless real diagonal series of a self-adjoint trace-class operator sums to its real
trace in every Hilbert basis. -/
theorem hasSum_realTrace {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (hself : IsSelfAdjoint T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => diagonalExpectationValue T hself (d i)) (hT.realTrace hself) := by
  have hcomplex :
      HasSum (fun i => ((diagonalExpectationValue T hself (d i) : ℝ) : ℂ))
        hT.trace := by
    exact HasSum.congr_fun (hT.hasSum_trace d) fun i =>
      coe_diagonalExpectationValue_right T hself (d i)
  rw [← hT.coe_realTrace hself] at hcomplex
  exact Complex.hasSum_ofReal.mp hcomplex

end IsTraceClass

section FiniteDimensional

variable [FiniteDimensional ℂ H]

/-- Every bounded operator on a finite-dimensional Hilbert space is trace class. -/
theorem isTraceClass_of_finiteDimensional (T : H →L[ℂ] H) : IsTraceClass T := by
  apply (isTraceClass_iff_isTraceClassWrt
    (stdOrthonormalBasis ℂ H).toHilbertBasis T).2
  exact Summable.of_finite

/-- In finite dimensions, the canonical trace agrees with the ordinary linear-map trace. -/
theorem IsTraceClass.trace_eq_linearMap_trace {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    hT.trace = LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) := by
  rw [hT.trace_eq_tsum_inner (stdOrthonormalBasis ℂ H).toHilbertBasis, tsum_fintype]
  simp only [OrthonormalBasis.coe_toHilbertBasis]
  exact (LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ H)).symm

end FiniteDimensional

end ContinuousLinearMap
