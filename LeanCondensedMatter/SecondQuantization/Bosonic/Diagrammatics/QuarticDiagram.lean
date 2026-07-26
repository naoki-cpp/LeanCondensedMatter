import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramReassemble
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticInteraction

set_option linter.style.header false

/-!
# Bosonic quartic diagrams

The bosonic diagram layer specializes the label-generic Common quartic-diagram machinery to
`Bosonic.QuarticVertexLabel`. Pairing graphs, connected components, restriction to a component, and
reassembly are inherited without any fermionic sign or CAR assumptions.
-/

namespace SecondQuantization
namespace Bosonic

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

end Bosonic
end SecondQuantization
