import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Vertex orders and ordered quartic Wick data

A `QuarticVertexOrder S` identifies the diagram's vertices with ordered slots `Fin S.card`.
`orderedLegToDiagramLeg` transports flattened leg positions between the slot enumeration and the
diagram's fixed enumeration, and `pairingInOrder` transports the pairing accordingly.

For a fixed vertex set and vertex order, `quarticWickDiagramEquivOrderedData` identifies a quartic
Wick diagram with a slot-indexed vertex-label sequence and a pairing in the same slot enumeration.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [Fintype Mode] {N : ℕ}

/-- A bijection between ordered slots and the diagram's vertex set. -/
abbrev QuarticVertexOrder (S : Finset (Fin N)) := Fin S.card ≃ (↥S)

/-- The flattened-leg relabeling induced by a vertex order. -/
noncomputable def orderedLegToDiagramLeg (S : Finset (Fin N)) (order : QuarticVertexOrder S) :
    Equiv.Perm (Fin (2 * (2 * S.card))) :=
  (orderedQuarticLegEquiv S.card).trans
    ((order.prodCongr (Equiv.refl (Fin 4))).trans (quarticLegEquiv S).symm)

/-- A diagram's pairing transported to a vertex order's slot enumeration. -/
noncomputable def QuarticWickDiagram.pairingInOrder {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S) :
    Common.BlochDeDominicis.Pairing (2 * S.card) :=
  d.pairing.relabel (orderedLegToDiagramLeg S order)

/-- Slot-indexed vertex labels together with a pairing in the same enumeration. -/
abbrev OrderedQuarticWickData (Mode : Type*) (n : ℕ) :=
  (Fin n → QuarticVertexLabel Mode) × Common.BlochDeDominicis.Pairing (2 * n)

/-- A diagram on `S` is equivalent to ordered data for any fixed vertex order. -/
noncomputable def quarticWickDiagramEquivOrderedData {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) :
    QuarticWickDiagram Mode N S ≃ OrderedQuarticWickData Mode S.card where
  toFun d := (fun i => d.vertexLabel (order i), d.pairingInOrder order)
  invFun x :=
    { vertexLabel := fun v => x.1 (order.symm v)
      pairing := x.2.relabel (orderedLegToDiagramLeg S order).symm }
  left_inv d := by
    apply QuarticWickDiagram.ext
    · funext v
      simp
    · simp [QuarticWickDiagram.pairingInOrder]
  right_inv x := by
    obtain ⟨labels, pairing⟩ := x
    refine Prod.ext ?_ ?_
    · funext i
      simp
    · simp [QuarticWickDiagram.pairingInOrder]

/-- Reindex a finite sum over diagrams as a sum over ordered data. -/
theorem sum_quarticWickDiagram_eq_sum_orderedData {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) (F : OrderedQuarticWickData Mode S.card → ℂ) :
    ∑ d : QuarticWickDiagram Mode N S, F (quarticWickDiagramEquivOrderedData order d) =
      ∑ x : OrderedQuarticWickData Mode S.card, F x :=
  Equiv.sum_comp (quarticWickDiagramEquivOrderedData order) F

omit [DecidableEq Mode] [Fintype Mode] in
/-- A vertex order exists for every finite vertex set. -/
noncomputable def someVertexOrder (S : Finset (Fin N)) : QuarticVertexOrder S :=
  ((Fintype.equivFin (↥S)).trans (finCongr (Fintype.card_coe S))).symm

omit [DecidableEq Mode] [Fintype Mode] in
/-- The number of vertex orders is `S.card!`. -/
theorem card_quarticVertexOrder (S : Finset (Fin N)) :
    Fintype.card (QuarticVertexOrder S) = S.card.factorial := by
  rw [Fintype.card_equiv (someVertexOrder S), Fintype.card_fin]

end SecondQuantization
