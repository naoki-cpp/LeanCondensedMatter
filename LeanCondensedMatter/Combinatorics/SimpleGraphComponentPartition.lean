import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Partition.Finpartition

set_option linter.style.header false

/-!
# Connected-component partitions of finite simple graphs

This module exposes the finite partition determined by graph reachability. It provides both the
ordinary partition of a finite vertex type and an ambient-finset view for graphs whose vertex type
is a subtype `↥s`.
-/

namespace SimpleGraph

variable {V : Type*}

open Classical in
/-- The partition of a finite graph's vertex type into connected components. -/
noncomputable def componentPartition [Fintype V] (G : SimpleGraph V) :
    Finpartition (Finset.univ : Finset V) :=
  Finpartition.ofSetoid G.reachableSetoid

open Classical in
/-- The connected-component block containing `v`. -/
noncomputable def componentBlock [Fintype V] (G : SimpleGraph V) (v : V) : Finset V :=
  G.componentPartition.part v

/-- Membership in a connected-component block is graph reachability. -/
theorem mem_componentBlock [Fintype V] (G : SimpleGraph V) (v w : V) :
    w ∈ G.componentBlock v ↔ G.Reachable w v := by
  classical
  change w ∈ (Finpartition.ofSetoid G.reachableSetoid).part v ↔ _
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  exact G.reachable_comm

@[simp]
theorem self_mem_componentBlock [Fintype V] (G : SimpleGraph V) (v : V) :
    v ∈ G.componentBlock v :=
  (G.mem_componentBlock v v).2 (Reachable.refl _)

/-- Every connected-component block occurs as a part of the component partition. -/
theorem componentBlock_mem_componentPartition [Fintype V] (G : SimpleGraph V) (v : V) :
    G.componentBlock v ∈ G.componentPartition.parts := by
  change G.componentPartition.part v ∈ G.componentPartition.parts
  exact G.componentPartition.part_mem.2 (Finset.mem_univ v)

/-- Reachable vertices determine the same connected-component block. -/
theorem componentBlock_eq_of_reachable [Fintype V] (G : SimpleGraph V) {v w : V}
    (h : G.Reachable v w) : G.componentBlock v = G.componentBlock w := by
  change G.componentPartition.part v = G.componentPartition.part w
  exact (G.componentPartition.mem_part_iff_part_eq_part
    (Finset.mem_univ v) (Finset.mem_univ w)).1 ((G.mem_componentBlock w v).2 h)

/-- Two component blocks are equal exactly when their base vertices are reachable. -/
theorem componentBlock_eq_iff_reachable [Fintype V] (G : SimpleGraph V) (v w : V) :
    G.componentBlock v = G.componentBlock w ↔ G.Reachable v w := by
  constructor
  · intro h
    apply (G.mem_componentBlock w v).1
    rw [← h]
    exact G.self_mem_componentBlock v
  · exact G.componentBlock_eq_of_reachable

/-- A vertex belongs to a component part exactly when its component block is that part. -/
theorem componentBlock_eq_iff_mem [Fintype V] (G : SimpleGraph V) {B : Finset V}
    (hB : B ∈ G.componentPartition.parts) (v : V) :
    G.componentBlock v = B ↔ v ∈ B := by
  change G.componentPartition.part v = B ↔ v ∈ B
  exact G.componentPartition.part_eq_iff_mem hB

section AmbientFinset

variable {α : Type*} {s : Finset α}

/-- Classify an ambient vertex by the connected component of its subtype vertex when it lies in
`s`. Vertices outside `s` are kept distinct and do not occur in `componentPartitionOn`. -/
private noncomputable def componentClassOn (G : SimpleGraph ↥s) (x : α) :
    α ⊕ G.ConnectedComponent :=
  if hx : x ∈ s then
    Sum.inr (G.connectedComponentMk ⟨x, hx⟩)
  else
    Sum.inl x

/-- Ambient equivalence relation induced by graph connectedness inside `s`. -/
private noncomputable def componentSetoidOn (G : SimpleGraph ↥s) : Setoid α :=
  Setoid.ker G.componentClassOn

private theorem componentSetoidOn_rel_iff_reachable (G : SimpleGraph ↥s) (v w : ↥s) :
    G.componentSetoidOn (v : α) (w : α) ↔ G.Reachable v w := by
  rw [componentSetoidOn, Setoid.ker_def]
  simp only [componentClassOn, dif_pos v.2, dif_pos w.2, Sum.inr.injEq]
  exact ConnectedComponent.eq

open Classical in
/-- The connected-component partition of a graph on `↥s`, viewed as a partition of the ambient
finset `s`. -/
noncomputable def componentPartitionOn (G : SimpleGraph ↥s) : Finpartition s :=
  Finpartition.ofSetSetoid G.componentSetoidOn s

open Classical in
/-- The connected-component block containing `v`, viewed as a finite subset of the ambient type. -/
noncomputable def componentBlockOn (G : SimpleGraph ↥s) (v : ↥s) : Finset α :=
  G.componentPartitionOn.part (v : α)

/-- Ambient membership in a component block is reachability from a vertex of `s`. -/
theorem mem_componentBlockOn (G : SimpleGraph ↥s) (v : ↥s) {x : α} :
    x ∈ G.componentBlockOn v ↔ ∃ hx : x ∈ s, G.Reachable ⟨x, hx⟩ v := by
  classical
  rw [componentBlockOn, componentPartitionOn, Finpartition.mem_part_ofSetSetoid_iff_rel]
  constructor
  · rintro ⟨_, hx, hrel⟩
    refine ⟨hx, ?_⟩
    exact ((G.componentSetoidOn_rel_iff_reachable v ⟨x, hx⟩).1 hrel).symm
  · rintro ⟨hx, hreach⟩
    exact ⟨v.2, hx, (G.componentSetoidOn_rel_iff_reachable v ⟨x, hx⟩).2 hreach.symm⟩

@[simp]
theorem self_mem_componentBlockOn (G : SimpleGraph ↥s) (v : ↥s) :
    (v : α) ∈ G.componentBlockOn v :=
  (G.mem_componentBlockOn v).2 ⟨v.2, Reachable.refl _⟩

/-- Every ambient component block occurs as a part of the component partition. -/
theorem componentBlockOn_mem_componentPartitionOn (G : SimpleGraph ↥s) (v : ↥s) :
    G.componentBlockOn v ∈ G.componentPartitionOn.parts := by
  change G.componentPartitionOn.part (v : α) ∈ G.componentPartitionOn.parts
  exact G.componentPartitionOn.part_mem.2 v.2

/-- Reachable subtype vertices determine the same ambient component block. -/
theorem componentBlockOn_eq_of_reachable (G : SimpleGraph ↥s) {v w : ↥s}
    (h : G.Reachable v w) : G.componentBlockOn v = G.componentBlockOn w := by
  change G.componentPartitionOn.part (v : α) = G.componentPartitionOn.part (w : α)
  exact (G.componentPartitionOn.mem_part_iff_part_eq_part v.2 w.2).1
    ((G.mem_componentBlockOn w).2 ⟨v.2, h⟩)

/-- An ambient vertex belongs to a component part exactly when its component block is that part. -/
theorem componentBlockOn_eq_iff_mem (G : SimpleGraph ↥s) {B : Finset α}
    (hB : B ∈ G.componentPartitionOn.parts) (v : ↥s) :
    G.componentBlockOn v = B ↔ (v : α) ∈ B := by
  change G.componentPartitionOn.part (v : α) = B ↔ (v : α) ∈ B
  exact G.componentPartitionOn.part_eq_iff_mem hB

/-- Every ambient component part is contained in the graph's vertex finset. -/
theorem componentPartOn_subset (G : SimpleGraph ↥s) {B : Finset α}
    (hB : B ∈ G.componentPartitionOn.parts) : B ⊆ s :=
  G.componentPartitionOn.le hB

end AmbientFinset

end SimpleGraph
