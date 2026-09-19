import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Diagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Ordered labelled quartic diagrams

A vertex order identifies a finite diagram's vertices with slots `Fin k`. The induced leg
equivalence transports the pairing to the same slot enumeration, giving an equivalence between a
labelled quartic diagram and slot-indexed labels together with a pairing. The common
`QuarticVertexOrder S` specialization takes `k = S.card`, but the transport itself does not require
that cardinality to appear definitionally in the slot type.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- A bijection between ordered slots and vertices of a finite vertex set. -/
abbrev QuarticVertexOrder (S : Finset (Fin N)) := Fin S.card ≃ ↥S

/-- A diagram's commutative vertex weight reindexed along a chosen vertex order. -/
theorem QuarticDiagram.vertexWeight_eq_prod_vertexLabel_order {M : Type*} [CommMonoid M]
    {S : Finset (Fin N)} {k : ℕ} (d : QuarticDiagram Label N S) (w : Label → M)
    (order : Fin k ≃ ↥S) :
    d.vertexWeight w = ∏ i : Fin k, w (d.vertexLabel (order i)) := by
  rw [QuarticDiagram.vertexWeight]
  exact (Equiv.prod_comp order (fun v => w (d.vertexLabel v))).symm

/-- The flattened-leg equivalence induced by a vertex order. -/
noncomputable def orderedLegToDiagramLeg (S : Finset (Fin N)) {k : ℕ}
    (order : Fin k ≃ ↥S) :
    Fin (2 * (2 * k)) ≃ Fin (2 * (2 * S.card)) :=
  (orderedQuarticLegEquiv k).trans
    ((order.prodCongr (Equiv.refl (Fin 4))).trans (quarticLegEquiv S).symm)

/-- A diagram's pairing transported to a vertex order's slot enumeration. -/
noncomputable def QuarticDiagram.pairingInOrder {S : Finset (Fin N)} {k : ℕ}
    (d : QuarticDiagram Label N S) (order : Fin k ≃ ↥S) :
    Combinatorics.Pairing (2 * k) :=
  d.pairing.transport (orderedLegToDiagramLeg S order)

/-- Slot-indexed labels together with a pairing in the same slot enumeration. -/
abbrev OrderedQuarticDiagramData (Label : Type*) (n : ℕ) :=
  (Fin n → Label) × Combinatorics.Pairing (2 * n)

/-- A labelled quartic diagram is equivalent to ordered data for any fixed vertex order. -/
noncomputable def quarticDiagramEquivOrderedData {S : Finset (Fin N)} {k : ℕ}
    (order : Fin k ≃ ↥S) :
    QuarticDiagram Label N S ≃ OrderedQuarticDiagramData Label k where
  toFun d := (fun i => d.vertexLabel (order i), d.pairingInOrder order)
  invFun x :=
    { vertexLabel := fun v => x.1 (order.symm v)
      pairing := x.2.transport (orderedLegToDiagramLeg S order).symm }
  left_inv d := by
    apply QuarticDiagram.ext
    · funext v
      simp
    · simp [QuarticDiagram.pairingInOrder]
  right_inv x := by
    obtain ⟨labels, pairing⟩ := x
    refine Prod.ext ?_ ?_
    · funext i
      simp
    · simp [QuarticDiagram.pairingInOrder]

/-- Reindex a finite sum over labelled diagrams as a sum over ordered data. -/
theorem sum_quarticDiagram_eq_sum_orderedData [Fintype Label] {S : Finset (Fin N)} {k : ℕ}
    (order : Fin k ≃ ↥S) (F : OrderedQuarticDiagramData Label k → ℂ) :
    ∑ d : QuarticDiagram Label N S, F (quarticDiagramEquivOrderedData order d) =
      ∑ x : OrderedQuarticDiagramData Label k, F x :=
  Equiv.sum_comp (quarticDiagramEquivOrderedData order) F

/-- A vertex order exists for every finite vertex set. -/
noncomputable def someVertexOrder (S : Finset (Fin N)) : QuarticVertexOrder S :=
  ((Fintype.equivFin (↥S)).trans (finCongr (Fintype.card_coe S))).symm

/-- The number of vertex orders is `S.card!`. -/
theorem card_quarticVertexOrder (S : Finset (Fin N)) :
    Fintype.card (QuarticVertexOrder S) = S.card.factorial := by
  rw [Fintype.card_equiv (someVertexOrder S), Fintype.card_fin]

end Common
end SecondQuantization
