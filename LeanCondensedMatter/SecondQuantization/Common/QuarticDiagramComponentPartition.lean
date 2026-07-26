import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramConnected
import Mathlib.Order.Partition.Finpartition

set_option linter.style.header false

/-!
# Connected-component partitions of labelled quartic diagrams

Connected-component blocks and their finite partition depend only on the diagram's pairing graph,
not on the vertex-label type or particle statistics.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

open Classical in
/-- The vertices reachable from `v`, viewed as a finite subset of the ambient vertex type. -/
noncomputable def QuarticDiagram.componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) : Finset (Fin N) :=
  (Finset.univ.filter fun w : ↥S => d.vertexGraph.Reachable w v).image Subtype.val

theorem QuarticDiagram.mem_componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) {x : Fin N} :
    x ∈ d.componentBlock v ↔ ∃ hx : x ∈ S, d.vertexGraph.Reachable ⟨x, hx⟩ v := by
  simp only [componentBlock, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hx, hreach⟩
    exact ⟨⟨x, hx⟩, hreach, rfl⟩

@[simp]
theorem QuarticDiagram.self_mem_componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) : (v : Fin N) ∈ d.componentBlock v :=
  (d.mem_componentBlock v).2 ⟨v.2, SimpleGraph.Reachable.refl _⟩

theorem QuarticDiagram.componentBlock_eq_of_reachable {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {v w : ↥S} (h : d.vertexGraph.Reachable v w) :
    d.componentBlock v = d.componentBlock w := by
  ext x
  simp only [mem_componentBlock]
  exact exists_congr fun _ => ⟨fun hv => hv.trans h, fun hw => hw.trans h.symm⟩

theorem QuarticDiagram.componentBlock_disjoint_of_not_reachable {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {v w : ↥S} (h : ¬ d.vertexGraph.Reachable v w) :
    Disjoint (d.componentBlock v) (d.componentBlock w) := by
  rw [Finset.disjoint_left]
  rintro x hxv hxw
  rw [mem_componentBlock] at hxv hxw
  obtain ⟨hx, hxv⟩ := hxv
  obtain ⟨_, hxw⟩ := hxw
  exact h (hxv.symm.trans hxw)

/-- The partition of `S` into connected components of the diagram's vertex graph. -/
noncomputable def QuarticDiagram.componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) : Finpartition S :=
  (Finpartition.ofPairwiseDisjoint ((Finset.univ : Finset ↥S).image d.componentBlock)
    (by
      rintro x hx y hy hxy
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := hy
      by_cases hr : d.vertexGraph.Reachable v w
      · exact absurd (d.componentBlock_eq_of_reachable hr) hxy
      · exact d.componentBlock_disjoint_of_not_reachable hr)).copy
    (by
      rw [Finset.sup_image, Function.id_comp]
      apply Finset.ext
      intro x
      simp only [Finset.mem_sup, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨v, hx⟩
        exact ((d.mem_componentBlock v).1 hx).1
      · intro hx
        exact ⟨⟨x, hx⟩, d.self_mem_componentBlock ⟨x, hx⟩⟩)

theorem QuarticDiagram.componentBlock_mem_componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) :
    d.componentBlock v ∈ d.componentPartition.parts := by
  simp only [componentPartition, Finpartition.copy_parts, Finpartition.ofPairwiseDisjoint_parts,
    Finset.mem_erase]
  refine ⟨?_, Finset.mem_image.2 ⟨v, Finset.mem_univ v, rfl⟩⟩
  rw [Finset.bot_eq_empty]
  exact Finset.ne_empty_of_mem (d.self_mem_componentBlock v)

theorem QuarticDiagram.exists_componentBlock_eq_of_mem {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : ∃ v : ↥S, d.componentBlock v = B := by
  simp only [componentPartition, Finpartition.copy_parts, Finpartition.ofPairwiseDisjoint_parts,
    Finset.mem_erase] at hB
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hB.2
  exact ⟨v, rfl⟩

end Common
end SecondQuantization
