import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentDecomposition

set_option linter.style.header false

/-!
# Order consequences of external connectedness

These small consequences of the Common two-point component decomposition are independent of particle
statistics and physical labels. They keep connected-series specializations from reproving finite-slot
facts on top of a statistics-specific diagram subtype.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*}

/-- For a standard order-`n` two-point diagram, external connectedness means that the canonical
external component contains all `n` interaction slots. -/
theorem TwoPointDiagram.interactionComponentSize_externalComponentPart_of_isExternallyConnected
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (hconn : d.IsExternallyConnected) :
    d.interactionComponentSize d.externalComponentPart = n := by
  have hsize : d.interactionComponentSize d.externalComponentPart =
      d.externalInteractionPart.card := rfl
  rw [hsize, (d.isExternallyConnected_iff_externalInteractionPart_eq).1 hconn]
  simp

/-- Every order-zero standard two-point diagram is externally connected: there are no interaction
slots that could belong to a vacuum component. -/
theorem TwoPointDiagram.isExternallyConnected_of_order_zero
    (d : TwoPointDiagram ExternalLabel InternalLabel 0 (Finset.univ : Finset (Fin 0))) :
    d.IsExternallyConnected := by
  rw [d.isExternallyConnected_iff_externalInteractionPart_eq]
  apply Finset.eq_univ_of_forall
  intro x
  exact x.elim0

end Common
end SecondQuantization
