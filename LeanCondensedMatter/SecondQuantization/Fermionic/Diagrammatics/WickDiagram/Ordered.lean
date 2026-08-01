import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Ordered
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram

set_option linter.style.header false

/-!
# Fermionic ordered quartic Wick data

Compatibility names specializing the statistics-independent ordered quartic-diagram API to
fermionic quartic vertex labels.
-/

namespace SecondQuantization

open Combinatorics

variable {Mode : Type*} [DecidableEq Mode] [Fintype Mode] {N : ℕ}

/-- A bijection between ordered slots and the diagram's vertex set. -/
abbrev QuarticVertexOrder (S : Finset (Fin N)) := Common.QuarticVertexOrder S

/-- The flattened-leg relabeling induced by a vertex order. -/
noncomputable abbrev orderedLegToDiagramLeg (S : Finset (Fin N)) (order : QuarticVertexOrder S) :
    Equiv.Perm (Fin (2 * (2 * S.card))) :=
  Common.orderedLegToDiagramLeg S order

/-- A fermionic diagram's pairing transported to a vertex order's slot enumeration. -/
noncomputable abbrev QuarticWickDiagram.pairingInOrder {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S) :
    Combinatorics.Pairing (2 * S.card) :=
  Common.QuarticDiagram.pairingInOrder d order

/-- Slot-indexed fermionic vertex labels and a pairing in the same enumeration. -/
abbrev OrderedQuarticWickData (Mode : Type*) (n : ℕ) :=
  Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) n

/-- A fermionic quartic Wick diagram is equivalent to ordered data. -/
noncomputable abbrev quarticWickDiagramEquivOrderedData {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) :
    QuarticWickDiagram Mode N S ≃ OrderedQuarticWickData Mode S.card :=
  Common.quarticDiagramEquivOrderedData order

/-- Reindex a sum over fermionic quartic Wick diagrams as a sum over ordered data. -/
theorem sum_quarticWickDiagram_eq_sum_orderedData {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) (F : OrderedQuarticWickData Mode S.card → ℂ) :
    ∑ d : QuarticWickDiagram Mode N S, F (quarticWickDiagramEquivOrderedData order d) =
      ∑ x : OrderedQuarticWickData Mode S.card, F x :=
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

end SecondQuantization
