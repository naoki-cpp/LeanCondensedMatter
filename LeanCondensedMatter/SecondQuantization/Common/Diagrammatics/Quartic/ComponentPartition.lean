import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Connected
import LeanCondensedMatter.Combinatorics.FinpartitionSetoid

set_option linter.style.header false

/-!
# Connected-component partitions of labelled quartic diagrams

Connected-component blocks and their finite partition depend only on the diagram's pairing graph,
not on the vertex-label type or particle statistics.

The graph itself lives on the subtype `↥S`, while the historical diagram-facing partition has parts
in the ambient type `Fin N`. We therefore classify ambient vertices by Mathlib connected components
inside `S` and use the kernel setoid of that classification with the generic setoid-finpartition API.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- Classify an ambient vertex by its graph connected component when it lies in `S`. Vertices outside
`S` are kept distinct; they do not occur in the resulting partition of `S`. -/
private noncomputable def QuarticDiagram.componentClass {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (x : Fin N) :
    Fin N ⊕ d.vertexGraph.ConnectedComponent :=
  if hx : x ∈ S then
    Sum.inr (d.vertexGraph.connectedComponentMk ⟨x, hx⟩)
  else
    Sum.inl x

/-- Ambient equivalence relation induced by the graph connected component inside `S`. -/
private noncomputable def QuarticDiagram.componentSetoid {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) : Setoid (Fin N) :=
  Setoid.ker d.componentClass

private theorem QuarticDiagram.componentSetoid_rel_iff_reachable {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v w : ↥S) :
    d.componentSetoid (v : Fin N) (w : Fin N) ↔ d.vertexGraph.Reachable v w := by
  rw [QuarticDiagram.componentSetoid, Setoid.ker_def]
  simp only [QuarticDiagram.componentClass, dif_pos v.2, dif_pos w.2, Sum.inr.injEq]
  exact SimpleGraph.ConnectedComponent.eq

/-- The partition of `S` into connected components of the diagram's vertex graph. -/
noncomputable def QuarticDiagram.componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) : Finpartition S :=
  d.componentSetoid.finpartitionOn S

/-- The component containing `v`, viewed as a finite subset of the ambient vertex type. -/
noncomputable def QuarticDiagram.componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) : Finset (Fin N) :=
  d.componentSetoid.blockOn S (v : Fin N)

theorem QuarticDiagram.mem_componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) {x : Fin N} :
    x ∈ d.componentBlock v ↔ ∃ hx : x ∈ S, d.vertexGraph.Reachable ⟨x, hx⟩ v := by
  rw [QuarticDiagram.componentBlock, Setoid.mem_blockOn_iff]
  constructor
  · rintro ⟨_, hx, hrel⟩
    refine ⟨hx, ?_⟩
    exact ((d.componentSetoid_rel_iff_reachable v ⟨x, hx⟩).1 hrel).symm
  · rintro ⟨hx, hreach⟩
    exact ⟨v.2, hx,
      (d.componentSetoid_rel_iff_reachable v ⟨x, hx⟩).2 hreach.symm⟩

@[simp]
theorem QuarticDiagram.self_mem_componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) : (v : Fin N) ∈ d.componentBlock v := by
  simpa [QuarticDiagram.componentBlock] using
    d.componentSetoid.self_mem_blockOn S v.2

/-- Every component block occurs as a part of the component partition. -/
theorem QuarticDiagram.componentBlock_mem_componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) :
    d.componentBlock v ∈ d.componentPartition.parts := by
  simpa [QuarticDiagram.componentBlock, QuarticDiagram.componentPartition] using
    d.componentSetoid.blockOn_mem_parts S v.2

/-- Reachable vertices determine the same component block. -/
theorem QuarticDiagram.componentBlock_eq_of_reachable {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {v w : ↥S} (h : d.vertexGraph.Reachable v w) :
    d.componentBlock v = d.componentBlock w := by
  have hrel : d.componentSetoid (v : Fin N) (w : Fin N) :=
    (d.componentSetoid_rel_iff_reachable v w).2 h
  simpa [QuarticDiagram.componentBlock] using
    (d.componentSetoid.blockOn_eq_iff_rel S v.2 w.2).2 hrel

/-- Two component blocks are equal exactly when their base vertices are reachable. -/
theorem QuarticDiagram.componentBlock_eq_iff_reachable {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v w : ↥S) :
    d.componentBlock v = d.componentBlock w ↔ d.vertexGraph.Reachable v w := by
  rw [QuarticDiagram.componentBlock]
  exact (d.componentSetoid.blockOn_eq_iff_rel S v.2 w.2).trans
    (d.componentSetoid_rel_iff_reachable v w)

/-- Non-reachable vertices determine disjoint component blocks. -/
theorem QuarticDiagram.componentBlock_disjoint_of_not_reachable {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {v w : ↥S} (h : ¬ d.vertexGraph.Reachable v w) :
    Disjoint (d.componentBlock v) (d.componentBlock w) := by
  have hrel : ¬ d.componentSetoid (v : Fin N) (w : Fin N) := by
    intro hrel
    exact h ((d.componentSetoid_rel_iff_reachable v w).1 hrel)
  simpa [QuarticDiagram.componentBlock] using
    d.componentSetoid.blockOn_disjoint_of_not_rel S v.2 w.2 hrel

/-- Every component-partition part is a component block. -/
theorem QuarticDiagram.exists_componentBlock_eq_of_mem {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : ∃ v : ↥S, d.componentBlock v = B := by
  change B ∈ (d.componentSetoid.finpartitionOn S).parts at hB
  obtain ⟨x, hxS, hx⟩ := d.componentSetoid.exists_blockOn_eq_of_mem S hB
  exact ⟨⟨x, hxS⟩, by simpa [QuarticDiagram.componentBlock] using hx⟩

/-- A vertex belongs to a component part exactly when its component block is that part. -/
theorem QuarticDiagram.componentBlock_eq_iff_mem {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥S) :
    d.componentBlock v = B ↔ (v : Fin N) ∈ B := by
  change d.componentSetoid.blockOn S (v : Fin N) = B ↔ (v : Fin N) ∈ B
  exact d.componentSetoid.blockOn_eq_iff_mem S hB (v : Fin N)

end Common
end SecondQuantization
