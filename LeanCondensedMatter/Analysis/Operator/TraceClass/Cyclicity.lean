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
  obtain ⟨A, B, hA, hB, hfactor⟩ :=
    (isTraceClass_iff_exists_hilbertSchmidt_factorization (T := T)).mp hT
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
      (hT.comp_right W).trace_eq_innerHS_of_factorization hfactorRight d
    _ = innerHS d (A * ContinuousLinearMap.adjoint W) B :=
      innerHS_comp_right d hA hB W
    _ = (hT.comp_left W).trace :=
      ((hT.comp_left W).trace_eq_innerHS_of_factorization hfactorLeft d).symm

end IsTraceClass

namespace IsHilbertSchmidt

/-- For Hilbert--Schmidt operators `A` and `B`, the canonical traces of `AB` and `BA`
agree. Both products are trace class. -/
theorem trace_mul_comm {A B : H →L[ℂ] H}
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    (hA.mul_isTraceClass hB).trace = (hB.mul_isTraceClass hA).trace := by
  obtain ⟨ι, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hfactorAB :
      ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint A) * B = A * B := by
    rw [ContinuousLinearMap.adjoint_adjoint]
  have hfactorBA :
      ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint B) * A = B * A := by
    rw [ContinuousLinearMap.adjoint_adjoint]
  calc
    (hA.mul_isTraceClass hB).trace =
        innerHS d (ContinuousLinearMap.adjoint A) B :=
      (hA.mul_isTraceClass hB).trace_eq_innerHS_of_factorization hfactorAB d
    _ = innerHS d (ContinuousLinearMap.adjoint B) A :=
      innerHS_adjoint_swap d hA hB
    _ = (hB.mul_isTraceClass hA).trace :=
      ((hB.mul_isTraceClass hA).trace_eq_innerHS_of_factorization hfactorBA d).symm

end IsHilbertSchmidt

end ContinuousLinearMap
