import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.SimpleGraph.Sum

set_option linter.style.header false

/-!
# Connected-component partitions of finite simple graphs

This module exposes the finite partition determined by graph reachability. It provides both the
ordinary partition of a finite vertex type and an ambient-finset view for graphs whose vertex type
is a subtype `↥s`. It also provides graph-sum reachability lemmas.
-/

namespace SimpleGraph

variable {V : Type*} [DecidableEq V]

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

omit [DecidableEq V] in
/-- Reachability between right-side vertices of a graph sum is exactly reachability
inside the right summand. -/
theorem reachable_sum_inr_iff
    {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (x y : W) :
    (G ⊕g H).Reachable (Sum.inr x) (Sum.inr y) ↔ H.Reachable x y := by
  classical
  constructor
  · rintro ⟨p⟩
    have hclosed (z : W) (w : V ⊕ W)
        (hadj : (G ⊕g H).Adj (Sum.inr z) w) :
        ∃ z' : W, w = Sum.inr z' := by
      cases w with
      | inl u =>
          exact False.elim
            (SimpleGraph.not_adj_sum_inl_inr u z ((G ⊕g H).adj_symm hadj))
      | inr u => exact ⟨u, rfl⟩
    have hlift :
        ∀ {u v : V ⊕ W}, (G ⊕g H).Walk u v →
          ∀ z : W, u = Sum.inr z →
            ∃ z' : W, v = Sum.inr z' ∧ H.Reachable z z' := by
      intro u v q
      induction q with
      | nil => exact fun z hz => ⟨z, hz, SimpleGraph.Reachable.refl _⟩
      | cons hadj q ih =>
          intro z hz
          subst hz
          obtain ⟨z', hz'⟩ := hclosed z _ hadj
          obtain ⟨y, hy, hreach⟩ := ih z' hz'
          refine ⟨y, hy, SimpleGraph.Reachable.trans ?_ hreach⟩
          exact SimpleGraph.Adj.reachable ((SimpleGraph.sum_adj_inr).1 (hz' ▸ hadj))
    obtain ⟨z, hz, hreach⟩ := hlift p x rfl
    exact (Sum.inr.inj hz).symm ▸ hreach
  · intro hreach
    exact hreach.map SimpleGraph.Embedding.sumInr.toHom

omit [DecidableEq V] in
/-- Reachability between left-side vertices of a graph sum is exactly reachability
inside the left summand. -/
theorem reachable_sum_inl_iff
    {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (x y : V) :
    (G ⊕g H).Reachable (Sum.inl x) (Sum.inl y) ↔ G.Reachable x y := by
  simpa [SimpleGraph.Iso.sumComm] using
    ((SimpleGraph.Iso.reachable_iff
      (φ := SimpleGraph.Iso.sumComm (G := G) (H := H))
      (u := Sum.inl x) (v := Sum.inl y)).symm.trans
        (SimpleGraph.reachable_sum_inr_iff H G x y))

omit [DecidableEq V] in
/-- A graph-sum isomorphism reflects reachability within the left summand. -/
theorem Iso.reachable_sum_inl_iff {W U : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph U}
    (φ : (G ⊕g H) ≃g K) (x y : V) :
    K.Reachable (φ (Sum.inl x)) (φ (Sum.inl y)) ↔ G.Reachable x y :=
  (SimpleGraph.Iso.reachable_iff
    (φ := φ) (u := Sum.inl x) (v := Sum.inl y)).trans
      (SimpleGraph.reachable_sum_inl_iff G H x y)

omit [DecidableEq V] in
/-- A graph-sum isomorphism reflects reachability within the right summand. -/
theorem Iso.reachable_sum_inr_iff {W U : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph U}
    (φ : (G ⊕g H) ≃g K) (x y : W) :
    K.Reachable (φ (Sum.inr x)) (φ (Sum.inr y)) ↔ H.Reachable x y :=
  (SimpleGraph.Iso.reachable_iff
    (φ := φ) (u := Sum.inr x) (v := Sum.inr y)).trans
      (SimpleGraph.reachable_sum_inr_iff G H x y)

section AmbientFinset

variable {α : Type*} [DecidableEq α] {s : Finset α}

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
  simp only [componentClassOn, dite_eq_left v.2, dite_eq_left w.2, Sum.inr.injEq]
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

/-- Reachable subtype vertices determine the same ambient component block. -/
theorem componentBlockOn_eq_of_reachable (G : SimpleGraph ↥s) {v w : ↥s}
    (h : G.Reachable v w) : G.componentBlockOn v = G.componentBlockOn w := by
  change G.componentPartitionOn.part (v : α) = G.componentPartitionOn.part (w : α)
  exact (G.componentPartitionOn.mem_part_iff_part_eq_part v.2 w.2).1
    ((G.mem_componentBlockOn w).2 ⟨v.2, h⟩)

end AmbientFinset

end SimpleGraph
