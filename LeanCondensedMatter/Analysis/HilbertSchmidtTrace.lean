import LeanCondensedMatter.Analysis.HilbertSchmidtInnerProduct

/-!
# Reconciling `innerHS` with `ContinuousLinearMap.trace`

For a compact self-adjoint trace-class operator, the Hilbert–Schmidt inner product against the
identity agrees with the eigenvalue-sum `trace` already defined in `TraceClassBasic.lean`. See
`notes/roadmaps/operator-algebra.md` (Track C, step 4).
-/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Reconciliation with `ContinuousLinearMap.trace`.** For a compact self-adjoint trace-class
`A`, the Hilbert–Schmidt inner product `innerHS d 1 A` — i.e. `Σᵢ ⟪dᵢ, A dᵢ⟫`, computed with `S`
taken to be the identity — agrees with `trace hAtc` (cast to `ℂ`). This is Track C's step 4
(`notes/roadmaps/operator-algebra.md`): it identifies the Hilbert–Schmidt route to a trace (needed
for the Born rule, where the relevant operator need not be self-adjoint) with the eigenvalue-sum
`trace` already defined for the self-adjoint case, on their common domain of applicability. -/
theorem innerHS_one_eq_trace {A : H →L[ℂ] H} (hAcpt : IsCompactOperator A) (hAsym : A.IsSymmetric)
    (hAtc : IsTraceClass A) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    innerHS d 1 A = (trace hAtc : ℂ) := by
  have hone : (fun i => (inner ℂ ((1 : H →L[ℂ] H) (d i)) (A (d i)) : ℂ)) =
      (fun i => (inner ℂ (d i) (A (d i)) : ℂ)) := by
    funext i
    rw [one_apply_eq_self]
  have hreal : ∀ i, (((inner ℂ (d i) (A (d i)) : ℂ)).re : ℂ) = (inner ℂ (d i) (A (d i)) : ℂ) :=
    fun i => by
      have hconj : starRingEnd ℂ (inner ℂ (d i) (A (d i)) : ℂ) = (inner ℂ (d i) (A (d i)) : ℂ) := by
        rw [inner_conj_symm]
        exact hAsym (d i) (d i)
      exact Complex.conj_eq_iff_re.mp hconj
  have hcast := (hasSum_inner_apply_eq_trace hAcpt hAsym hAtc d).mapL Complex.ofRealCLM
  simp only [Complex.ofRealCLM_apply] at hcast
  simp_rw [hreal] at hcast
  unfold innerHS
  rw [hone]
  exact hcast.tsum_eq

end ContinuousLinearMap
