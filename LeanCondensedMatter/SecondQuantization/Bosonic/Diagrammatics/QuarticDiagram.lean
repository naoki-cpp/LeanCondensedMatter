import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Reassemble
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticInteraction

set_option linter.style.header false

/-!
# Bosonic quartic diagrams

The bosonic diagram layer specializes the label-generic Common quartic-diagram machinery to
`Bosonic.QuarticVertexLabel`. It provides the basic and connected diagram types, component
restriction and reassembly, vertex orders, ordered pairing data, and finite-sum reindexing.

Pairing graphs and component proofs are inherited without fermionic sign or CAR assumptions.
-/

namespace SecondQuantization
namespace Bosonic

open Combinatorics

variable {Mode : Type*} {N : ℕ}

/-- A bosonic quartic diagram on the interaction vertices in `S`. -/
abbrev QuarticDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Common.QuarticDiagram (QuarticVertexLabel Mode) N S

/-- A connected bosonic quartic diagram. -/
abbrev ConnectedQuarticDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Common.ConnectedQuarticDiagram (QuarticVertexLabel Mode) N S

/-- The pairing-induced graph of a bosonic quartic diagram. -/
noncomputable abbrev QuarticDiagram.vertexGraph {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) : SimpleGraph (↥S) :=
  Common.QuarticDiagram.vertexGraph d

/-- Connectedness of a bosonic quartic diagram. -/
abbrev QuarticDiagram.IsConnected {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) : Prop :=
  Common.QuarticDiagram.IsConnected d

/-- The partition of the vertex set into pairing-graph components. -/
noncomputable abbrev QuarticDiagram.componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) : Finpartition S :=
  Common.QuarticDiagram.componentPartition d

/-- Restrict a bosonic quartic diagram to one component part. -/
noncomputable abbrev QuarticDiagram.restrictComponent {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : QuarticDiagram Mode N B :=
  Common.QuarticDiagram.restrictComponent d hB

/-- Restrict to one component and package the resulting connected diagram. -/
noncomputable abbrev QuarticDiagram.restrictComponentConnected {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : ConnectedQuarticDiagram Mode N B :=
  Common.QuarticDiagram.restrictComponentConnected d hB

/-- Restriction to a component part is connected. -/
theorem QuarticDiagram.restrictComponent_isConnected {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    (d.restrictComponent hB).IsConnected :=
  Common.QuarticDiagram.restrictComponent_isConnected d hB

/-- Reassemble a bosonic quartic diagram from connected diagrams on a partition's parts. -/
noncomputable def QuarticDiagram.reassemble {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Mode N (B : Finset (Fin N))) :
    QuarticDiagram Mode N S :=
  Common.QuarticDiagram.reassemble π F

variable [DecidableEq Mode] [Fintype Mode]

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
