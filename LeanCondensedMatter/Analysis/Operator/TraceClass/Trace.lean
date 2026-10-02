import LeanCondensedMatter.Analysis.Operator.TraceClass.Norm
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.InnerProduct
import LeanCondensedMatter.Analysis.Operator.Polar

set_option linter.style.header false

/-!
# Trace of general trace-class operators

The trace is the basis-independent complex diagonal sum of a trace-class bounded operator. A
private polar-factor argument factors a trace-class operator as `A† B` with `A` and `B`
Hilbert--Schmidt; the Hilbert--Schmidt inner-product API then supplies absolute convergence and
basis independence.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The totalized complex diagonal series of an operator in a chosen Hilbert basis. Outside
trace-class membership this is only a totalized `tsum`. -/
noncomputable def traceSeriesWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) : ℂ :=
  ∑' i, inner ℂ (d i) (T (d i))

/-- Every trace-class operator factors as `A† B` with Hilbert--Schmidt factors. -/
theorem IsTraceClass.exists_hilbertSchmidt_factorization
    {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    ∃ A B : H →L[ℂ] H,
      IsHilbertSchmidt A ∧ IsHilbertSchmidt B ∧ ContinuousLinearMap.adjoint A * B = T := by
  obtain ⟨U, hU, -, -⟩ := exists_leftPolarFactor T
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  have hS : IsHilbertSchmidt S := hT
  have hSself : IsSelfAdjoint S := (CFC.sqrt_nonneg (CFC.abs T)).isSelfAdjoint
  have hSS : S * S = CFC.abs T :=
    CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
  let A : H →L[ℂ] H := S * ContinuousLinearMap.adjoint U
  have hA : IsHilbertSchmidt A :=
    isHilbertSchmidt_comp_right hS (ContinuousLinearMap.adjoint U)
  have hAdjA : ContinuousLinearMap.adjoint A = U * S := by
    rw [show ContinuousLinearMap.adjoint A = star A from
      (ContinuousLinearMap.star_eq_adjoint A).symm]
    dsimp [A]
    rw [star_mul, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.star_eq_adjoint,
      hSself.adjoint_eq]
  refine ⟨A, S, hA, hS, ?_⟩
  rw [hAdjA, mul_assoc, hSS, hU]

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
  obtain ⟨A, B, hA, hB, hfactor⟩ := hT.exists_hilbertSchmidt_factorization
  have hsum := summable_inner_apply_of_isHilbertSchmidtWrt d
    (hA.isHilbertSchmidtWrt d) (hB.isHilbertSchmidtWrt d)
  exact hsum.congr fun i => (diagonal_eq_hilbertSchmidt_inner hfactor (d i)).symm

/-- The norms of the complex diagonal terms of a trace-class operator are summable in every
Hilbert basis. -/
theorem IsTraceClass.summable_norm_traceSeriesWrt {T : H →L[ℂ] H}
    (hT : IsTraceClass T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖inner ℂ (d i) (T (d i))‖) :=
  (hT.summable_traceSeriesWrt d).norm

/-- For a trace-class operator, the complex diagonal series has the same value in every Hilbert
basis. -/
theorem traceSeriesWrt_eq {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    traceSeriesWrt d T = traceSeriesWrt f T := by
  obtain ⟨A, B, hA, hB, hfactor⟩ := hT.exists_hilbertSchmidt_factorization
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

/-- The trace is independent of the proof of trace-class membership. -/
theorem trace_proof_irrel {T : H →L[ℂ] H} (hT hT' : IsTraceClass T) :
    hT.trace = hT'.trace := by
  exact congrArg trace (Subsingleton.elim hT hT')

end IsTraceClass

end ContinuousLinearMap
