import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Connected
import LeanCondensedMatter.Combinatorics.SimpleGraphComponentPartition

set_option linter.style.header false

/-!
# Connected-component partitions of labelled quartic diagrams

Connected-component blocks and their finite partition depend only on the diagram's pairing graph,
not on the vertex-label type or particle statistics. The diagram-facing API keeps parts in the
ambient type `Fin N`, while the generic graph construction is owned by `Combinatorics`.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- The partition of `S` into connected components of the diagram's vertex graph. -/
noncomputable def QuarticDiagram.componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) : Finpartition S :=
  d.vertexGraph.componentPartitionOn

/-- The component containing `v`, viewed as a finite subset of the ambient vertex type. -/
noncomputable def QuarticDiagram.componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) : Finset (Fin N) :=
  d.vertexGraph.componentBlockOn v

theorem QuarticDiagram.mem_componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) {x : Fin N} :
    x ∈ d.componentBlock v ↔ ∃ hx : x ∈ S, d.vertexGraph.Reachable ⟨x, hx⟩ v := by
  simpa only [QuarticDiagram.componentBlock] using d.vertexGraph.mem_componentBlockOn v

@[simp]
theorem QuarticDiagram.self_mem_componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) : (v : Fin N) ∈ d.componentBlock v := by
  simpa only [QuarticDiagram.componentBlock] using d.vertexGraph.self_mem_componentBlockOn v

/-- Every component block occurs as a part of the component partition. -/
theorem QuarticDiagram.componentBlock_mem_componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) :
    d.componentBlock v ∈ d.componentPartition.parts := by
  simpa only [QuarticDiagram.componentBlock, QuarticDiagram.componentPartition] using
    d.vertexGraph.componentBlockOn_mem_componentPartitionOn v

/-- Reachable vertices determine the same component block. -/
theorem QuarticDiagram.componentBlock_eq_of_reachable {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {v w : ↥S} (h : d.vertexGraph.Reachable v w) :
    d.componentBlock v = d.componentBlock w := by
  simpa only [QuarticDiagram.componentBlock] using
    d.vertexGraph.componentBlockOn_eq_of_reachable h

/-- A vertex belongs to a component part exactly when its component block is that part. -/
theorem QuarticDiagram.componentBlock_eq_iff_mem {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥S) :
    d.componentBlock v = B ↔ (v : Fin N) ∈ B := by
  simpa only [QuarticDiagram.componentBlock, QuarticDiagram.componentPartition] using
    d.vertexGraph.componentBlockOn_eq_iff_mem hB v

/-- Every component part is contained in the ambient vertex set. -/
theorem QuarticDiagram.componentPart_subset {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : B ⊆ S := by
  simpa only [QuarticDiagram.componentPartition] using d.vertexGraph.componentPartOn_subset hB

end Common
end SecondQuantization
