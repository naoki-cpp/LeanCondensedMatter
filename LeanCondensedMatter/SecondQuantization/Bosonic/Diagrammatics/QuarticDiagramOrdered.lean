import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramOrdered
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticDiagram

set_option linter.style.header false

/-!
# Ordered bosonic quartic diagrams

Bosonic compatibility names for the statistics-independent ordered quartic-diagram construction.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode] [Fintype Mode] {N : ℕ}

/-- A bijection between ordered slots and a bosonic diagram's vertex set. -/
abbrev QuarticVertexOrder (S : Finset (Fin N)) := Common.QuarticVertexOrder S

/-- The flattened-leg relabeling induced by a bosonic vertex order. -/
noncomputable abbrev orderedLegToDiagramLeg (S : Finset (Fin N))
    (order : QuarticVertexOrder S) : Equiv.Perm (Fin (2 * (2 * S.card))) :=
  Common.orderedLegToDiagramLeg S order

/-- A bosonic diagram's pairing transported to a vertex order's slot enumeration. -/
noncomputable abbrev QuarticDiagram.pairingInOrder {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) (order : QuarticVertexOrder S) :
    Common.BlochDeDominicis.Pairing (2 * S.card) :=
  Common.QuarticDiagram.pairingInOrder d order

/-- Slot-indexed bosonic vertex labels and a pairing in the same enumeration. -/
abbrev OrderedQuarticDiagramData (Mode : Type*) (n : ℕ) :=
  Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) n

/-- A bosonic quartic diagram is equivalent to ordered data. -/
noncomputable abbrev quarticDiagramEquivOrderedData {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) :
    QuarticDiagram Mode N S ≃ OrderedQuarticDiagramData Mode S.card :=
  Common.quarticDiagramEquivOrderedData order

omit [DecidableEq Mode] in
/-- Reindex a sum over bosonic quartic diagrams as a sum over ordered data. -/
theorem sum_quarticDiagram_eq_sum_orderedData {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) (F : OrderedQuarticDiagramData Mode S.card → ℂ) :
    ∑ d : QuarticDiagram Mode N S, F (quarticDiagramEquivOrderedData order d) =
      ∑ x : OrderedQuarticDiagramData Mode S.card, F x :=
  Common.sum_quarticDiagram_eq_sum_orderedData order F

omit [DecidableEq Mode] [Fintype Mode] in
/-- A vertex order exists for every finite vertex set. -/
noncomputable def someVertexOrder (S : Finset (Fin N)) : QuarticVertexOrder S :=
  Common.someVertexOrder S

omit [DecidableEq Mode] [Fintype Mode] in
/-- The number of vertex orders is `S.card!`. -/
theorem card_quarticVertexOrder (S : Finset (Fin N)) :
    Fintype.card (QuarticVertexOrder S) = S.card.factorial :=
  Common.card_quarticVertexOrder S

end Bosonic
end SecondQuantization
