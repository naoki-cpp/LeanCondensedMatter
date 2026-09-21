import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirst

set_option linter.style.header false

/-!
# Fermionic quartic operator products

Operator-product identities that expand an interaction-picture quartic vertex into its four
time-evolved local-leg operators. This layer is separate from the flattened leg-family semantics
because it depends on the list-composition API `Common.prodComp`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [Fintype Mode] in
/-- A single evolved quartic vertex is the composed product of its four individually evolved local
legs in the canonical local-leg order. -/
theorem interactionPicture_quarticVertexOperator_eq_prodComp (ε : Mode → ℝ)
    (q : QuarticVertexLabel Mode) (τ : ℝ) :
    interactionPicture ε (quarticVertexOperator q) τ =
      Common.prodComp
        (List.ofFn (fun l : Fin 4 => imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l))) := by
  change Common.heisenbergEvolve (fermionEnergy ε) τ
      ((create q.create₁).comp
        ((create q.create₂).comp ((annihilate q.annihilate₂).comp (annihilate q.annihilate₁)))) = _
  simp only [← Module.End.mul_eq_comp, map_mul]
  simp [Module.End.mul_eq_comp, Common.prodComp, quarticLocalLegOperator,
    Common.quarticLocalLegOperator, List.ofFn_succ, imaginaryTimeEvolve]

end Fermionic
end SecondQuantization
