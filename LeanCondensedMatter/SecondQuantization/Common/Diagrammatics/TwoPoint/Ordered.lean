import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Ordered
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Ordered two-point diagrams

An interaction-vertex order identifies an arbitrary finite interaction set with explicit slots while
leaving the two distinguished external vertices fixed.  The induced leg relabeling transports the
pairing to the same ordered slot convention used by the finite-order two-point Dyson expansion.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- Ordered two-point legs for `n` interaction slots. -/
abbrev OrderedTwoPointLegData (n : ℕ) : Type :=
  Fin 2 ⊕ (Fin n × Fin 4)

/-- Relabel ordered interaction-slot legs to the vertices selected by `order`. -/
def twoPointInteractionOrderLegEquiv {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) :
    OrderedTwoPointLegData S.card ≃ TwoPointLeg S where
  toFun
    | Sum.inl e => Sum.inl e
    | Sum.inr (v, l) => Sum.inr (order v, l)
  invFun
    | Sum.inl e => Sum.inl e
    | Sum.inr (v, l) => Sum.inr (order.symm v, l)
  left_inv x := by rcases x with e | ⟨v, l⟩ <;> simp
  right_inv x := by rcases x with e | ⟨v, l⟩ <;> simp

/-- Flattened ordered positions mapped to the ambient diagram positions.  The equivalence maps new
ordered positions to old diagram positions, matching the convention of `Pairing.relabel`. -/
noncomputable def orderedTwoPointLegToDiagramLeg {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) :
    Equiv.Perm (Fin (2 * (2 * S.card + 1))) :=
  (twoPointLegEquiv (Finset.univ : Finset (Fin S.card))).trans <|
    (by
      simpa [OrderedTwoPointLegData] using
        (twoPointInteractionOrderLegEquiv order).trans (twoPointLegEquiv S).symm)

/-- Pairing of a two-point diagram transported to an explicit interaction-vertex order. -/
noncomputable def TwoPointDiagram.pairingInInteractionOrder {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) : Pairing (2 * S.card + 1) :=
  (by
    simpa using d.pairing).relabel (orderedTwoPointLegToDiagramLeg order)

/-- Ordered data of a two-point diagram: external labels, slot-indexed interaction labels, and the
pairing in the same slot enumeration. -/
abbrev OrderedTwoPointDiagramData (ExternalLabel InternalLabel : Type*) (n : ℕ) :=
  (Fin 2 → ExternalLabel) × (Fin n → InternalLabel) × Pairing (2 * n + 1)

/-- A finite two-point diagram is equivalent to ordered data for every fixed interaction order. -/
noncomputable def twoPointDiagramEquivOrderedData {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) :
    TwoPointDiagram ExternalLabel InternalLabel N S ≃
      OrderedTwoPointDiagramData ExternalLabel InternalLabel S.card where
  toFun d := (d.externalLabel, fun i => d.vertexLabel (order i), d.pairingInInteractionOrder order)
  invFun x :=
    { externalLabel := x.1
      vertexLabel := fun v => x.2.1 (order.symm v)
      pairing := by
        let p : Pairing (2 * S.card + 1) :=
          x.2.2.relabel (orderedTwoPointLegToDiagramLeg order).symm
        simpa using p }
  left_inv d := by
    apply TwoPointDiagram.ext
    · rfl
    · funext v
      simp
    · change (by
          let p : Pairing (2 * S.card + 1) :=
            (d.pairingInInteractionOrder order).relabel
              (orderedTwoPointLegToDiagramLeg order).symm
          simpa using p) = d.pairing
      simp [TwoPointDiagram.pairingInInteractionOrder]
  right_inv x := by
    rcases x with ⟨external, labels, pairing⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        simp
      · simp [TwoPointDiagram.pairingInInteractionOrder]

end Common
end SecondQuantization
