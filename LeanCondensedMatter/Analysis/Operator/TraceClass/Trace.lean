import LeanCondensedMatter.Analysis.Operator.TraceClass.Factorization.Basic

set_option linter.style.header false

/-!
# Trace of general trace-class operators

The trace is the basis-independent complex diagonal sum of a trace-class bounded operator.
Hilbert--Schmidt factorization supplies absolute convergence and basis independence. Public
basis-facing results use the diagonal series directly rather than a separate wrapper definition.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem diagonal_eq_hilbertSchmidt_inner
    {T A B : H →L[ℂ] H} (hfactor : ContinuousLinearMap.adjoint A * B = T)
    (x : H) :
    inner ℂ x (T x) = inner ℂ (A x) (B x) := by
  calc
    inner ℂ x (T x) = inner ℂ x ((ContinuousLinearMap.adjoint A * B) x) := by
      rw [hfactor]
    _ = inner ℂ x ((ContinuousLinearMap.adjoint A) (B x)) := by
      rw [mul_apply_eq_comp]
    _ = inner ℂ (A x) (B x) :=
      ContinuousLinearMap.adjoint_inner_right A x (B x)

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

/-- The canonical trace depends only on the underlying operator, not on the supplied
trace-class witnesses. -/
theorem trace_congr {T R : H →L[ℂ] H}
    (hT : IsTraceClass T) (hR : IsTraceClass R) (h : T = R) :
    hT.trace = hR.trace := by
  subst R
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  calc
    hT.trace = ∑' i, inner ℂ (d i) (T (d i)) := hT.trace_eq_tsum_inner d
    _ = hR.trace := (hR.trace_eq_tsum_inner d).symm

/-- The canonical trace is independent of the proof of trace-class membership. -/
theorem trace_proof_irrel {T : H →L[ℂ] H} (hT hT' : IsTraceClass T) :
    hT.trace = hT'.trace :=
  trace_congr hT hT' rfl

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

end ContinuousLinearMap
