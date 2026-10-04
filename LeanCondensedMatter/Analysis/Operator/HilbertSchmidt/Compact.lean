import LeanCondensedMatter.Analysis.Operator.Compact
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Norm

set_option linter.style.header false

/-!
# Compactness of Hilbert--Schmidt operators

Hilbert--Schmidt operators are compact. The proof first records the standard pointwise bound by the
Hilbert--Schmidt norm-square, then approximates the range by finite sums of rank-one projections.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsHilbertSchmidt

/-- Pointwise Hilbert--Schmidt bound:
`‖T x‖² ≤ ‖x‖² ∑ᵢ ‖T† dᵢ‖² = normSq(T) ‖x‖²`. -/
theorem norm_apply_sq_le_normSq_mul {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (x : H) :
    ‖T x‖ ^ 2 ≤ hT.normSq * ‖x‖ ^ 2 := by
  obtain ⟨ι, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  let hTadj : IsHilbertSchmidt (ContinuousLinearMap.adjoint T) :=
    isHilbertSchmidt_adjoint hT
  have hparse :
      HasSum (fun i : ι => ‖(inner ℂ (T x) (d i) : ℂ)‖ ^ 2) (‖T x‖ ^ 2) :=
    d.hasSum_norm_sq_inner (T x)
  have hcoeff :
      Summable (fun i : ι => ‖(inner ℂ (T x) (d i) : ℂ)‖ ^ 2) :=
    hparse.summable
  have hadj :
      Summable (fun i : ι => ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2) :=
    (isHilbertSchmidt_iff_isHilbertSchmidtWrt d (ContinuousLinearMap.adjoint T)).mp hTadj
  have hmajor :
      Summable (fun i : ι => ‖x‖ ^ 2 * ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2) :=
    hadj.mul_left (‖x‖ ^ 2)
  rw [← hparse.tsum_eq]
  calc
    (∑' i : ι, ‖(inner ℂ (T x) (d i) : ℂ)‖ ^ 2) ≤
        ∑' i : ι, ‖x‖ ^ 2 * ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2 := by
      exact hcoeff.tsum_le_tsum (fun i => by
        have hi :
            ‖(inner ℂ (T x) (d i) : ℂ)‖ ≤
              ‖x‖ * ‖(ContinuousLinearMap.adjoint T) (d i)‖ := by
          rw [← ContinuousLinearMap.adjoint_inner_right T x (d i)]
          exact norm_inner_le_norm x ((ContinuousLinearMap.adjoint T) (d i))
        calc
          ‖(inner ℂ (T x) (d i) : ℂ)‖ ^ 2 ≤
              (‖x‖ * ‖(ContinuousLinearMap.adjoint T) (d i)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hi 2
          _ = ‖x‖ ^ 2 * ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2 := by ring) hmajor
    _ = ‖x‖ ^ 2 * ∑' i : ι, ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2 := by
      rw [tsum_mul_left]
    _ = ‖x‖ ^ 2 * hTadj.normSq := by
      rw [hTadj.normSq_eq_seriesWrt d]
      rfl
    _ = hT.normSq * ‖x‖ ^ 2 := by
      rw [show hTadj.normSq = hT.normSq by
        exact IsHilbertSchmidt.normSq_proof_irrel hTadj
          (isHilbertSchmidt_adjoint hT) |>.trans (hT.normSq_adjoint)]
      ring

end IsHilbertSchmidt

end ContinuousLinearMap
