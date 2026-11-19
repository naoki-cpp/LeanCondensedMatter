import LeanCondensedMatter.Analysis.Operator.TraceClass.Diagonal
import LeanCondensedMatter.Analysis.Operator.TraceClass.Norm

set_option linter.style.header false

/-!
# Trace-norm error of a diagonal coordinate compression

For any nonnegative summable diagonal weights, the trace-norm loss under a
coordinate projection is exactly the discarded weight.  This statement does not
refer to a Gibbs density, particle number, or the completed Fock construction.
-/

noncomputable section

namespace HilbertBasis

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open Classical in
/-- The trace-norm error of a positive summable diagonal operator under a
coordinate projection is exactly the sum of the omitted diagonal weights.
Both operators are characterized on an arbitrary Hilbert basis; no finite-rank
or finite-dimensional assumption is required. -/
theorem traceNorm_sub_compress_diagonal
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hw : Summable (fun i => ‖w i‖)) (hw_nonneg : ∀ i, 0 ≤ w i)
    (T Q : H →L[ℂ] H) (P : ι → Prop)
    (hTdiag : ∀ i, T (b i) = (w i : ℂ) • b i)
    (hQdiag : ∀ i, Q (b i) = if P i then b i else 0) :
    ∃ hres : IsTraceClass (T - Q.comp (T.comp Q)),
      hres.traceNorm = ∑' i, if P i then 0 else w i := by
  classical
  let a : ι → ℝ := fun i => if P i then 0 else w i
  have ha : Summable (fun i => ‖a i‖) := by
    refine Summable.of_norm_bounded hw ?_
    intro i
    by_cases hi : P i <;> simp [a, hi]
  have ha_nonneg : ∀ i, 0 ≤ a i := by
    intro i
    by_cases hi : P i
    · simp [a, hi]
    · simpa [a, hi] using hw_nonneg i
  let D := b.diagonalOp (fun i => (a i : ℂ))
  have hD : IsTraceClass D := b.diagonalOp_isTraceClass a ha ha_nonneg
  have hDpos : D.IsPositive := b.diagonalOp_isPositive a ha ha_nonneg
  have hDnorm : hD.traceNorm = ∑' i, a i := by
    have h := hD.hasSum_diagonalExpectationValue_eq_traceNorm hDpos b
    have h' : HasSum a hD.traceNorm := by
      apply HasSum.congr_fun h
      intro i
      simpa only [D] using
        (b.diagonalExpectationValue_diagonalOp a ha ha_nonneg i).symm
    exact h'.tsum_eq.symm
  have hOp : T - Q.comp (T.comp Q) = D := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
    rintro _ ⟨i, rfl⟩
    have hDdiag : D (b i) = (a i : ℂ) • b i := by
      simpa only [D] using
        (b.diagonalOp_apply_basis (fun j => (a j : ℂ))
          (by simpa using ha) i)
    change T (b i) - Q (T (Q (b i))) = D (b i)
    rw [hDdiag, hTdiag i]
    by_cases hi : P i
    · rw [hQdiag i, if_pos hi, hTdiag i, map_smul, hQdiag i, if_pos hi]
      simp [a, hi] <;> exact sub_self _
    · rw [hQdiag i, if_neg hi, map_zero, map_zero]
      simp [a, hi]
  have hres : IsTraceClass (T - Q.comp (T.comp Q)) := by
    rw [hOp]
    exact hD
  refine ⟨hres, ?_⟩
  calc
    hres.traceNorm = hD.traceNorm :=
      IsTraceClass.traceNorm_congr hres hD hOp
    _ = ∑' i, a i := hDnorm
    _ = _ := rfl

end HilbertBasis
