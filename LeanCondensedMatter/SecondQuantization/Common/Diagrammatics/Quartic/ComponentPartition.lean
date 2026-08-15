import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Connected
import Mathlib.Order.Partition.Finpartition

set_option linter.style.header false

/-!
# Connected-component partitions of labelled quartic diagrams

Connected-component blocks and their finite partition depend only on the diagram's pairing graph,
not on the vertex-label type or particle statistics.

The graph itself lives on the subtype `↥S`, while the historical diagram-facing partition has parts
in the ambient type `Fin N`. We therefore classify ambient vertices by Mathlib connected components
inside `S` and use the kernel setoid of that classification with `Finpartition.ofSetSetoid`.
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

open Classical in
/-- The partition of `S` into connected components of the diagram's vertex graph. -/
noncomputable def QuarticDiagram.componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) : Finpartition S :=
  Finpartition.ofSetSetoid d.componentSetoid S

/-- The component containing `v`, viewed as a finite subset of the ambient vertex type. -/
noncomputable def QuarticDiagram.componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) : Finset (Fin N) :=
  d.componentPartition.part (v : Fin N)

theorem QuarticDiagram.mem_componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) {x : Fin N} :
    x ∈ d.componentBlock v ↔ ∃ hx : x ∈ S, d.vertexGraph.Reachable ⟨x, hx⟩ v := by
  rw [QuarticDiagram.componentBlock, QuarticDiagram.componentPartition,
    Finpartition.mem_part_ofSetSetoid_iff_rel]
  constructor
  · rintro ⟨_, hx, hrel⟩
    refine ⟨hx, ?_⟩
    exact ((d.componentSetoid_rel_iff_reachable v ⟨x, hx⟩).1 hrel).symm
  · rintro ⟨hx, hreach⟩
    exact ⟨v.2, hx, (d.componentSetoid_rel_iff_reachable v ⟨x, hx⟩).2 hreach.symm⟩

@[simp]
theorem QuarticDiagram.self_mem_componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) : (v : Fin N) ∈ d.componentBlock v :=
  (d.mem_componentBlock v).2 ⟨v.2, SimpleGraph.Reachable.refl _⟩

/-- Every component block occurs as a part of the component partition. -/
theorem QuarticDiagram.componentBlock_mem_componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) :
    d.componentBlock v ∈ d.componentPartition.parts := by
  change d.componentPartition.part (v : Fin N) ∈ d.componentPartition.parts
  exact d.componentPartition.part_mem.2 v.2

/-- Reachable vertices determine the same component block. -/
theorem QuarticDiagram.componentBlock_eq_of_reachable {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {v w : ↥S} (h : d.vertexGraph.Reachable v w) :
    d.componentBlock v = d.componentBlock w := by
  change d.componentPartition.part (v : Fin N) = d.componentPartition.part (w : Fin N)
  exact (d.componentPartition.mem_part_iff_part_eq_part v.2 w.2).1
    ((d.mem_componentBlock w).2 ⟨v.2, h⟩)

/-- Non-reachable vertices determine disjoint component blocks. -/
theorem QuarticDiagram.componentBlock_disjoint_of_not_reachable {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {v w : ↥S} (h : ¬ d.vertexGraph.Reachable v w) :
    Disjoint (d.componentBlock v) (d.componentBlock w) := by
  apply d.componentPartition.disjoint
  · exact d.componentBlock_mem_componentPartition v
  · exact d.componentBlock_mem_componentPartition w
  · intro hEq
    apply h
    have hmem : (v : Fin N) ∈ d.componentBlock w := by
      change (v : Fin N) ∈ d.componentPartition.part (w : Fin N)
      rw [← hEq]
      exact d.componentPartition.mem_part v.2
    obtain ⟨hv, hreach⟩ := (d.mem_componentBlock w).1 hmem
    have hvEq : (⟨(v : Fin N), hv⟩ : ↥S) = v := Subtype.ext (by rfl)
    rwa [hvEq] at hreach

/-- Every component-partition part is a component block. -/
theorem QuarticDiagram.exists_componentBlock_eq_of_mem {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : ∃ v : ↥S, d.componentBlock v = B := by
  obtain ⟨x, hxS, hx⟩ := d.componentPartition.part_surjOn hB
  refine ⟨⟨x, hxS⟩, ?_⟩
  simpa only [QuarticDiagram.componentBlock] using hx

end Common
end SecondQuantization
