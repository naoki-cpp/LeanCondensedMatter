import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops.Basic

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
  have hfactorRight :
      ContinuousLinearMap.adjoint A * (B * W) = T * W := by
    rw [← mul_assoc, hfactor]
  have hAdjAW :
      ContinuousLinearMap.adjoint (A * ContinuousLinearMap.adjoint W) =
        W * ContinuousLinearMap.adjoint A := by
    simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star]
  have hfactorLeft :
      ContinuousLinearMap.adjoint (A * ContinuousLinearMap.adjoint W) * B = W * T := by
    rw [hAdjAW, mul_assoc, hfactor]
  calc
    (hT.comp_right W).trace = innerHS d A (B * W) :=
      trace_eq_innerHS_of_factorization (hT.comp_right W) hfactorRight d
    _ = innerHS d (A * ContinuousLinearMap.adjoint W) B :=
      innerHS_comp_right d hA hB W
    _ = (hT.comp_left W).trace :=
      (trace_eq_innerHS_of_factorization (hT.comp_left W) hfactorLeft d).symm

end IsTraceClass

end ContinuousLinearMap
