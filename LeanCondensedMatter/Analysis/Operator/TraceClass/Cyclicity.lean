import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops

set_option linter.style.header false

/-!
# Cyclicity of the general trace-class trace

The canonical complex trace is cyclic when one factor is trace class and the other is bounded.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsTraceClass

/-- If `T` is trace class and `W` is bounded, then `Tr(TW) = Tr(WT)`. -/
theorem trace_comp_comm {T : H →L[ℂ] H} (hT : IsTraceClass T) (W : H →L[ℂ] H) :
    (hT.comp_right W).trace = (hT.comp_left W).trace := by
  obtain ⟨A, B, hA, hB, hfactor⟩ := hT.exists_hilbertSchmidt_factorization
  obtain ⟨ι, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hBW : IsHilbertSchmidt (B * W) := isHilbertSchmidt_comp_right hB W
  have hAW : IsHilbertSchmidt (A * ContinuousLinearMap.adjoint W) :=
    isHilbertSchmidt_comp_right hA (ContinuousLinearMap.adjoint W)
  have hfactorRight :
      ContinuousLinearMap.adjoint A * (B * W) = T * W := by
    rw [← mul_assoc, hfactor]
  have hAdjAW :
      ContinuousLinearMap.adjoint (A * ContinuousLinearMap.adjoint W) =
        W * ContinuousLinearMap.adjoint A := by
    rw [show ContinuousLinearMap.adjoint (A * ContinuousLinearMap.adjoint W) =
      star (A * ContinuousLinearMap.adjoint W) from
      (ContinuousLinearMap.star_eq_adjoint (A * ContinuousLinearMap.adjoint W)).symm]
    rw [star_mul, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.star_eq_adjoint]
  have hfactorLeft :
      ContinuousLinearMap.adjoint (A * ContinuousLinearMap.adjoint W) * B = W * T := by
    rw [hAdjAW, mul_assoc, hfactor]
  calc
    (hT.comp_right W).trace = innerHS d A (B * W) :=
      (hT.comp_right W).trace_eq_innerHS_of_hilbertSchmidt_factorization
        hA hBW hfactorRight d
    _ = innerHS d (A * ContinuousLinearMap.adjoint W) B :=
      innerHS_comp_right d hA hB W
    _ = (hT.comp_left W).trace :=
      ((hT.comp_left W).trace_eq_innerHS_of_hilbertSchmidt_factorization
        hAW hB hfactorLeft d).symm

/-- Products of two Hilbert--Schmidt operators have cyclic traces. The trace-class witnesses for
the two products may be supplied independently. -/
theorem trace_mul_comm_of_hilbertSchmidt
    {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T)
    (hST : IsTraceClass (S * T)) (hTS : IsTraceClass (T * S)) :
    hST.trace = hTS.trace := by
  obtain ⟨ι, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hSad : IsHilbertSchmidt (ContinuousLinearMap.adjoint S) :=
    isHilbertSchmidt_adjoint hS
  have hTad : IsHilbertSchmidt (ContinuousLinearMap.adjoint T) :=
    isHilbertSchmidt_adjoint hT
  have hfactorST :
      ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint S) * T = S * T := by
    rw [ContinuousLinearMap.adjoint_adjoint]
  have hfactorTS :
      ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint T) * S = T * S := by
    rw [ContinuousLinearMap.adjoint_adjoint]
  have hpair := summable_inner_adjoint_apply_and_tsum_eq d d
    (hSad.isHilbertSchmidtWrt d) (hT.isHilbertSchmidtWrt d)
  have hinner :
      innerHS d (ContinuousLinearMap.adjoint S) T =
        innerHS d (ContinuousLinearMap.adjoint T) S := by
    unfold innerHS
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hpair.2.symm
  calc
    hST.trace = innerHS d (ContinuousLinearMap.adjoint S) T :=
      hST.trace_eq_innerHS_of_hilbertSchmidt_factorization hSad hT hfactorST d
    _ = innerHS d (ContinuousLinearMap.adjoint T) S := hinner
    _ = hTS.trace :=
      (hTS.trace_eq_innerHS_of_hilbertSchmidt_factorization hTad hS hfactorTS d).symm

end IsTraceClass

end ContinuousLinearMap
