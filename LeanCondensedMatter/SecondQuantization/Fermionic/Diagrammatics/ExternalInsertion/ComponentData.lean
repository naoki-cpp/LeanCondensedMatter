import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.TimedField

set_option linter.style.header false

/-!
# Component-local fermionic external-insertion data

A restricted external-insertion component retains its interaction vertices as a subset of the
ambient slots. The concrete fermionic amplitude layer instead uses consecutive `Fin m` interaction
slots. This module supplies the canonical increasing reindexing needed to apply that amplitude to
one connected component, together with the induced local external and interaction times.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*}

/-- Reindex one connected component by consecutive interaction slots while preserving the canonical
component external order and restricted pairing. -/
noncomputable def ExternalInsertionWickDiagram.componentWickDiagram {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts) :
    ExternalInsertionWickDiagram Mode (d.externalPairCount B)
      (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card := by
  let T :=
    interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  let r := d.restrictComponent B
  exact {
    externalLabel := r.externalLabel
    vertexLabel := fun v => r.vertexLabel (T.orderIsoOfFin rfl v.1)
    pairing := Equiv.cast (by simp) r.pairing
  }

/-- External times of one component in its canonical increasing external-slot order. -/
noncomputable def ExternalInsertionWickDiagram.componentExternalTime {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    Fin (2 * d.externalPairCount B) → ℝ :=
  fun e => externalTime (d.externalSectorOrderIso B e).1

/-- Interaction times of one component in canonical increasing local interaction-slot order. -/
noncomputable def ExternalInsertionWickDiagram.componentInteractionTime {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    Fin (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card → ℝ :=
  fun v =>
    σ ((interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).orderIsoOfFin
        rfl v).1

@[simp]
theorem ExternalInsertionWickDiagram.componentWickDiagram_externalLabel {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts)
    (e : Fin (2 * d.externalPairCount B)) :
    (d.componentWickDiagram B).externalLabel e =
      d.externalLabel (d.externalSectorOrderIso B e).1 := by
  rfl

end Fermionic
end SecondQuantization
