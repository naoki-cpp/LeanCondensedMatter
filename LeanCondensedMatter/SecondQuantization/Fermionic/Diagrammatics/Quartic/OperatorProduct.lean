import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.QuarticInteraction

set_option linter.style.header false

/-!
# Fermionic quartic operator products

Operator-product identities that expand an interaction-picture quartic vertex into its four
time-evolved local-leg operators. This layer is separate from the flattened leg-family semantics
and uses Mathlib's canonical `List.prod` composition on endomorphisms.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [Fintype Mode] in
/-- A single evolved quartic vertex is the composed product of its four individually evolved local
legs in the canonical local-leg order. -/
theorem interactionPicture_quarticVertexOperator_eq_prod (ε : Mode → ℝ)
    (q : QuarticVertexLabel Mode) (τ : ℝ) :
    interactionPicture ε (quarticVertexOperator q) τ =
      (List.ofFn (fun l : Fin 4 =>
        imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l))).prod := by
  change Common.heisenbergEvolve (fermionEnergy ε) τ
      ((create q.create₁).comp
        ((create q.create₂).comp ((annihilate q.annihilate₂).comp (annihilate q.annihilate₁)))) = _
  simp only [← Module.End.mul_eq_comp, map_mul]
  simp [Module.End.mul_eq_comp, Module.End.one_eq_id, quarticLocalLegOperator,
    Common.quarticLocalLegOperator, List.ofFn_succ, imaginaryTimeEvolve]

end Fermionic
end SecondQuantization
