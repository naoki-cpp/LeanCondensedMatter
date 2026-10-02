import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Basic

set_option linter.style.header false

/-!
# Hilbert--Schmidt norm-square series

This module owns the basis-relative totalized series
`Σᵢ ‖T dᵢ‖²`. For Hilbert--Schmidt operators its value is independent of the Hilbert basis.
The unrestricted definition is a totalized `tsum`; outside Hilbert--Schmidt membership it is not
assigned Hilbert--Schmidt norm meaning.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The totalized square-norm series of `T` in a Hilbert basis. -/
noncomputable def hilbertSchmidtNormSqSeriesWrt {ι : Type*}
    (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : ℝ :=
  ∑' i, ‖T (d i)‖ ^ 2

/-- For a Hilbert--Schmidt operator, the square-norm series has the same value in every Hilbert
basis. -/
theorem hilbertSchmidtNormSqSeriesWrt_eq {ι κ : Type*}
    (d : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ H)
    (T : H →L[ℂ] H) (hT : IsHilbertSchmidt T) :
    hilbertSchmidtNormSqSeriesWrt d T = hilbertSchmidtNormSqSeriesWrt f T := by
  unfold hilbertSchmidtNormSqSeriesWrt
  exact (summable_norm_sq_apply_and_tsum_eq d f T (hT.isHilbertSchmidtWrt d)).2.symm

namespace IsHilbertSchmidt

/-- The basis-independent squared Hilbert--Schmidt norm. -/
noncomputable def normSq {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) : ℝ :=
  let w : Set H := Classical.choose hT
  let hw : ∃ d : HilbertBasis w ℂ H, IsHilbertSchmidtWrt d T :=
    Classical.choose_spec hT
  let d : HilbertBasis w ℂ H := Classical.choose hw
  hilbertSchmidtNormSqSeriesWrt d T

/-- The squared Hilbert--Schmidt norm is the square-norm series in every Hilbert basis. -/
theorem normSq_eq_seriesWrt {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.normSq = hilbertSchmidtNormSqSeriesWrt d T := by
  unfold normSq
  exact hilbertSchmidtNormSqSeriesWrt_eq _ d T hT

omit [CompleteSpace H] in
/-- The squared Hilbert--Schmidt norm is independent of the proof of membership. -/
theorem normSq_proof_irrel {T : H →L[ℂ] H} (hT hT' : IsHilbertSchmidt T) :
    hT.normSq = hT'.normSq := by
  exact congrArg normSq (Subsingleton.elim hT hT')

omit [CompleteSpace H] in
/-- The squared Hilbert--Schmidt norm is nonnegative. -/
theorem normSq_nonneg {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    0 ≤ hT.normSq := by
  unfold normSq hilbertSchmidtNormSqSeriesWrt
  exact tsum_nonneg fun _ => sq_nonneg _

/-- Taking the adjoint preserves the squared Hilbert--Schmidt norm. -/
theorem normSq_adjoint {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    (isHilbertSchmidt_adjoint hT).normSq = hT.normSq := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [(isHilbertSchmidt_adjoint hT).normSq_eq_seriesWrt d, hT.normSq_eq_seriesWrt d]
  unfold hilbertSchmidtNormSqSeriesWrt
  exact (summable_norm_sq_adjoint_apply_and_tsum_eq d d T
    (hT.isHilbertSchmidtWrt d)).2

/-- Left composition by a bounded operator increases the squared Hilbert--Schmidt norm by at most
the square of the operator norm. -/
theorem normSq_comp_left_le (hT : IsHilbertSchmidt T) (B : H →L[ℂ] H) :
    (isHilbertSchmidt_comp_left B hT).normSq ≤ ‖B‖ ^ 2 * hT.normSq := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [(isHilbertSchmidt_comp_left B hT).normSq_eq_seriesWrt d,
    hT.normSq_eq_seriesWrt d]
  unfold hilbertSchmidtNormSqSeriesWrt
  have hTsum : Summable (fun i => ‖T (d i)‖ ^ 2) := hT.isHilbertSchmidtWrt d
  have hBTsum : Summable (fun i => ‖(B * T) (d i)‖ ^ 2) :=
    (isHilbertSchmidt_comp_left B hT).isHilbertSchmidtWrt d
  have hscaled : Summable (fun i => ‖B‖ ^ 2 * ‖T (d i)‖ ^ 2) :=
    hTsum.mul_left (‖B‖ ^ 2)
  calc
    (∑' i, ‖(B * T) (d i)‖ ^ 2) ≤ ∑' i, ‖B‖ ^ 2 * ‖T (d i)‖ ^ 2 := by
      exact hBTsum.tsum_le_tsum (fun i => by
        have hle : ‖(B * T) (d i)‖ ≤ ‖B‖ * ‖T (d i)‖ := by
          rw [mul_apply_eq_comp]
          exact B.le_opNorm (T (d i))
        calc
          ‖(B * T) (d i)‖ ^ 2 ≤ (‖B‖ * ‖T (d i)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hle 2
          _ = ‖B‖ ^ 2 * ‖T (d i)‖ ^ 2 := by ring) hscaled
    _ = ‖B‖ ^ 2 * ∑' i, ‖T (d i)‖ ^ 2 := by
      rw [tsum_mul_left]

/-- Right composition by a bounded operator increases the squared Hilbert--Schmidt norm by at most
the square of the operator norm. -/
theorem normSq_comp_right_le (hT : IsHilbertSchmidt T) (B : H →L[ℂ] H) :
    (isHilbertSchmidt_comp_right hT B).normSq ≤ ‖B‖ ^ 2 * hT.normSq := by
  let hTB : IsHilbertSchmidt (T * B) := isHilbertSchmidt_comp_right hT B
  let hTadj : IsHilbertSchmidt (ContinuousLinearMap.adjoint T) :=
    isHilbertSchmidt_adjoint hT
  let hleft : IsHilbertSchmidt
      (ContinuousLinearMap.adjoint B * ContinuousLinearMap.adjoint T) :=
    isHilbertSchmidt_comp_left (ContinuousLinearMap.adjoint B) hTadj
  have hadj_eq :
      ContinuousLinearMap.adjoint (T * B) =
        ContinuousLinearMap.adjoint B * ContinuousLinearMap.adjoint T := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint, star_mul]
  calc
    (isHilbertSchmidt_comp_right hT B).normSq = hTB.normSq :=
      IsHilbertSchmidt.normSq_proof_irrel _ _
    _ = (isHilbertSchmidt_adjoint hTB).normSq :=
      (IsHilbertSchmidt.normSq_adjoint hTB).symm
    _ = hleft.normSq := by
      rw [hadj_eq]
      exact IsHilbertSchmidt.normSq_proof_irrel _ _
    _ ≤ ‖ContinuousLinearMap.adjoint B‖ ^ 2 * hTadj.normSq :=
      IsHilbertSchmidt.normSq_comp_left_le hTadj (ContinuousLinearMap.adjoint B)
    _ = ‖B‖ ^ 2 * hT.normSq := by
      rw [← ContinuousLinearMap.star_eq_adjoint, norm_star,
        IsHilbertSchmidt.normSq_adjoint hT]

end IsHilbertSchmidt

end ContinuousLinearMap
