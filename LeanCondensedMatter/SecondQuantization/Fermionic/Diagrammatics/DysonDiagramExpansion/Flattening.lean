import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LegFamily
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic

set_option linter.style.header false

/-!
# Dyson diagram expansion: operator flattening
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode]

/-! ## Flattening `Common.quarticVertexSequenceInteractionPicture` into a `4n`-atom `List.prod` -/

/-- The ordered product of the flattened evolved quartic legs is exactly the Common
interaction-picture quartic-vertex sequence. The row-major `4n` product decomposition is owned by
`Common.prod_orderedQuarticLegFamily_eq_vertexProducts`; this theorem supplies only the fermionic
imaginary-time specialization. -/
theorem prod_ofFn_quarticLegOperatorForSequence_eq_quarticVertexSequenceInteractionPicture
    (ε : Mode → ℝ) :
    ∀ (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ),
      List.prod (List.ofFn (quarticLegOperatorForSequence ε q τ)) =
        Common.quarticVertexSequenceInteractionPicture (fermionEnergy ε) create annihilate n q τ := by
  intro n q τ
  change
    (List.ofFn (Common.orderedQuarticLegFamily
      (fun i : Fin n => fun l : Fin 4 =>
        Common.heisenbergEvolve (fermionEnergy ε) (τ i)
          (Common.quarticLocalLegOperator create annihilate (q i) l)))).prod =
      (List.ofFn (fun i : Fin n =>
        Common.heisenbergEvolve (fermionEnergy ε) (τ i)
          (Common.quarticVertexOperator create annihilate (q i)))).prod
  rw [Common.prod_orderedQuarticLegFamily_eq_vertexProducts]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact (Common.heisenbergEvolve_quarticVertexOperator_eq_prod
    (fermionEnergy ε) create annihilate (q i) (τ i)).symm

end Fermionic
end SecondQuantization
