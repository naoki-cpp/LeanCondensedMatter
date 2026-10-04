import LeanCondensedMatter.Analysis.Operator.TraceClass.Factorization

set_option linter.style.header false

/-!
# Trace of general trace-class operators

The trace is the basis-independent complex diagonal sum of a trace-class bounded operator.
Hilbert--Schmidt factorization supplies absolute convergence and basis independence; the
factorization itself is owned by `TraceClass/Factorization.lean`.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The totalized complex diagonal series of an operator in a chosen Hilbert basis. Outside
trace-class membership this is only a totalized `tsum`. -/
noncomputable def traceSeriesWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) : ℂ :=
  ∑' i, inner ℂ (d i) (T (d i))

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
theorem IsTraceClass.summable_traceSeriesWrt {T : H →L[ℂ] H}
    (hT : IsTraceClass T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    Summable (fun i => inner ℂ (d i) (T (d i))) := by
  obtain ⟨A, B, hA, hB, hfactor⟩ :=
    (isTraceClass_iff_exists_hilbertSchmidt_factorization (T := T)).mp hT
  have hsum := hA.summable_inner_apply hB d
  exact hsum.congr fun i => (diagonal_eq_hilbertSchmidt_inner hfactor (d i)).symm

/-- For a trace-class operator, the complex diagonal series has the same value in every Hilbert
basis. -/
private theorem traceSeriesWrt_eq {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    traceSeriesWrt d T = traceSeriesWrt f T := by
  obtain ⟨A, B, hA, hB, hfactor⟩ :=
    (isTraceClass_iff_exists_hilbertSchmidt_factorization (T := T)).mp hT
  have hd : traceSeriesWrt d T = innerHS d A B := by
    unfold traceSeriesWrt innerHS
    apply tsum_congr
    intro i
    exact diagonal_eq_hilbertSchmidt_inner hfactor (d i)
  have hf : traceSeriesWrt f T = innerHS f A B := by
    unfold traceSeriesWrt innerHS
    apply tsum_congr
    intro i
    exact diagonal_eq_hilbertSchmidt_inner hfactor (f i)
  rw [hd, hf]
  exact innerHS_eq_of_isHilbertSchmidt d f hA hB

namespace IsTraceClass

/-- The basis-independent complex trace of a trace-class operator. -/
noncomputable def trace {T : H →L[ℂ] H} (hT : IsTraceClass T) : ℂ :=
  let w : Set H := Classical.choose hT
  let hw : ∃ d : HilbertBasis w ℂ H,
      IsHilbertSchmidtWrt d (CFC.sqrt (CFC.abs T)) := Classical.choose_spec hT
  let d : HilbertBasis w ℂ H := Classical.choose hw
  traceSeriesWrt d T

/-- The trace is the complex diagonal series in every Hilbert basis. -/
theorem trace_eq_seriesWrt {T : H →L[ℂ] H} (hT : IsTraceClass T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.trace = traceSeriesWrt d T := by
  unfold trace
  exact traceSeriesWrt_eq _ d T hT

end IsTraceClass

end ContinuousLinearMap
