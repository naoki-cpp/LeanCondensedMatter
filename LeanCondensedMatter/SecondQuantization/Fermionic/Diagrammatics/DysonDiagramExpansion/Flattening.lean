import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LegFamily
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg

set_option linter.style.header false

/-!
# Dyson diagram expansion: operator flattening
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-! ## Flattening `Common.quarticVertexSequenceInteractionPicture` into a `4n`-atom `List.prod` -/

omit [Fintype Mode] in
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
        imaginaryTimeEvolve ε (τ i) (quarticLocalLegOperator (q i) l)))).prod = _
  rw [Common.prod_orderedQuarticLegFamily_eq_vertexProducts]
  unfold Common.quarticVertexSequenceInteractionPicture
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  symm
  simpa [Common.interactionPicture, interactionPicture, quarticVertexOperator,
    imaginaryTimeEvolve, quarticLocalLegOperator] using
    (Common.heisenbergEvolve_quarticVertexOperator_eq_prod
      (fermionEnergy ε) create annihilate (q i) (τ i))

end Fermionic
end SecondQuantization
