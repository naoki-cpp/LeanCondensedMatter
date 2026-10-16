import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.CutSides
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.SeparatingPaths

set_option linter.style.header false

/-!
# Canonical ordering of separating propagators

A separating propagator cuts a connected two-point diagram into exactly two
components, canonically distinguished by the external vertices. The source-side
component blocks of two such cuts are comparable by inclusion, without choosing
a path from external vertex zero to external vertex one.

The key elementary fact is that deleting an edge whose endpoints both lie
outside the connected component of a root cannot change which vertices the
root reaches. It is kept private here until a general graph-level consumer
requires it.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S : Finset (Fin N)}

/-- A walk reachable from a root cannot use an edge whose two endpoints
are outside the root's connected component. -/
private theorem reachable_deleteEdges_of_endpoints_outside
    {V : Type*} (G : SimpleGraph V) (removed : Sym2 V)
    (root a b target : V)
    (ha : ¬ (G.deleteEdges {removed}).Reachable root a)
    (hb : ¬ (G.deleteEdges {removed}).Reachable root b)
    (h : (G.deleteEdges {removed}).Reachable root target) :
    (G.deleteEdges {s(a, b)}).Reachable root target := by
  let H := G.deleteEdges {removed}
  have transport {u v : V} (p : H.Walk u v)
      (hu : H.Reachable root u) :
      (G.deleteEdges {s(a, b)}).Reachable u v := by
    induction p with
    | nil =>
        exact SimpleGraph.Reachable.refl _
    | @cons u v w hadj p ih =>
        have hv : H.Reachable root v :=
          hu.trans (SimpleGraph.Adj.reachable hadj)
        have hadj' : (G.deleteEdges {s(a, b)}).Adj u v := by
          have hG : G.Adj u v := (SimpleGraph.deleteEdges_adj).1 hadj |>.1
          apply (SimpleGraph.deleteEdges_adj).2
          refine ⟨hG, ?_⟩
          intro hbad
          have heq : s(u, v) = s(a, b) := Set.mem_singleton_iff.mp hbad
          rcases (Sym2.eq_iff).1 heq with ⟨hua, _⟩ | ⟨hub, _⟩
          · exact ha (hua ▸ hu)
          · exact hb (hub ▸ hu)
        exact (SimpleGraph.Adj.reachable hadj').trans (ih hv)
  exact h.elim fun p => transport p (SimpleGraph.Reachable.refl root)

/-- The source-side components of any two external-separating propagators are
nested. This statement includes the case when both legs name the same paired
propagator, and does not assume the propagators are internal; the later 1PI
decomposition specializes it to internal-to-internal cuts.

In particular, ordering the source sides by inclusion is independent of any
chosen external walk. -/
theorem TwoPointDiagram.externalSource_componentBlocks_comparable
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (cut₁ cut₂ : Fin (2 * (2 * S.card + 1)))
    (hsep₁ : ¬ (d.vertexGraphWithoutPropagator cut₁).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hsep₂ : ¬ (d.vertexGraphWithoutPropagator cut₂).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    (d.vertexGraphWithoutPropagator cut₁).componentBlock (Sum.inl (0 : Fin 2)) ⊆
      (d.vertexGraphWithoutPropagator cut₂).componentBlock (Sum.inl (0 : Fin 2)) ∨
    (d.vertexGraphWithoutPropagator cut₂).componentBlock (Sum.inl (0 : Fin 2)) ⊆
      (d.vertexGraphWithoutPropagator cut₁).componentBlock (Sum.inl (0 : Fin 2)) := by
  classical
  let s₀ : TwoPointVertex S := Sum.inl (0 : Fin 2)
  let t₁ : TwoPointVertex S := Sum.inl (1 : Fin 2)
  let H₁ := d.vertexGraphWithoutPropagator cut₁
  let H₂ := d.vertexGraphWithoutPropagator cut₂
  let e₁ : Sym2 (TwoPointVertex S) :=
    s(twoPointVertexOfLeg cut₁, twoPointVertexOfLeg (d.pairing.partner cut₁))
  let a : TwoPointVertex S := twoPointVertexOfLeg cut₂
  let b : TwoPointVertex S := twoPointVertexOfLeg (d.pairing.partner cut₂)
  let e₂ : Sym2 (TwoPointVertex S) := s(a, b)
  have hdel₁ : d.vertexGraph.deleteEdges {e₁} = H₁ :=
    d.deleteEdges_eq_vertexGraphWithoutPropagator_of_separatingCut hconnected cut₁ hsep₁
  have hdel₂ : d.vertexGraph.deleteEdges {e₂} = H₂ :=
    d.deleteEdges_eq_vertexGraphWithoutPropagator_of_separatingCut hconnected cut₂ hsep₂
  have hseparation₁ : ¬ H₁.Reachable s₀ t₁ := hsep₁
  have hseparation₂ : ¬ H₂.Reachable s₀ t₁ := hsep₂
  have hside (v : TwoPointVertex S) :
      H₁.Reachable s₀ v ∨ H₁.Reachable t₁ v :=
    d.reachable_external_side_withoutPropagator hconnected cut₁ hsep₁ v
  have transport (root v : TwoPointVertex S)
      (ha : ¬ H₁.Reachable root a)
      (hb : ¬ H₁.Reachable root b)
      (hv : H₁.Reachable root v) : H₂.Reachable root v := by
    have hr := reachable_deleteEdges_of_endpoints_outside
      d.vertexGraph e₁ root a b v
      (by simpa only [hdel₁] using ha)
      (by simpa only [hdel₁] using hb)
      (by simpa only [hdel₁] using hv)
    change (d.vertexGraph.deleteEdges {e₂}).Reachable root v at hr
    rw [hdel₂] at hr
    exact hr
  by_cases heq : e₁ = e₂
  · left
    have hgraph : H₁ = H₂ := by
      calc
        H₁ = d.vertexGraph.deleteEdges {e₁} := hdel₁.symm
        _ = d.vertexGraph.deleteEdges {e₂} := by rw [heq]
        _ = H₂ := hdel₂
    intro v hv
    change v ∈ H₁.componentBlock s₀ at hv
    change v ∈ H₂.componentBlock s₀
    rw [hgraph] at hv
    exact hv
  · have hG : d.vertexGraph.Adj a b := by
      apply (d.isBridge_of_separatingCut hconnected cut₂ hsep₂).reachable_iff_adj.mp
      exact (d.preconnected_iff_isExternallyConnected).2 hconnected a b
    have hab : H₁.Adj a b := by
      rw [← hdel₁]
      apply (SimpleGraph.deleteEdges_adj).2
      refine ⟨hG, ?_⟩
      intro hbad
      exact heq (Set.mem_singleton_iff.mp hbad).symm
    rcases hside a with h₀a | h₁a
    · have h₀b : H₁.Reachable s₀ b :=
        h₀a.trans (SimpleGraph.Adj.reachable hab)
      right
      intro v hv
      have hv₂ : H₂.Reachable s₀ v := ((H₂.mem_componentBlock s₀ v).1 hv).symm
      rcases hside v with hv₀ | hv₁
      · exact (H₁.mem_componentBlock s₀ v).2 hv₀.symm
      · have hna : ¬ H₁.Reachable t₁ a :=
          fun h => hseparation₁ (h₀a.trans h.symm)
        have hnb : ¬ H₁.Reachable t₁ b :=
          fun h => hseparation₁ (h₀b.trans h.symm)
        have hv₂t : H₂.Reachable t₁ v := transport t₁ v hna hnb hv₁
        exact False.elim (hseparation₂ (hv₂.trans hv₂t.symm))
    · have h₁b : H₁.Reachable t₁ b :=
        h₁a.trans (SimpleGraph.Adj.reachable hab)
      left
      intro v hv
      have hv₁ : H₁.Reachable s₀ v := ((H₁.mem_componentBlock s₀ v).1 hv).symm
      have hna : ¬ H₁.Reachable s₀ a :=
        fun h => hseparation₁ (h.trans h₁a.symm)
      have hnb : ¬ H₁.Reachable s₀ b :=
        fun h => hseparation₁ (h.trans h₁b.symm)
      exact (H₂.mem_componentBlock s₀ v).2
        (transport s₀ v hna hnb hv₁).symm


/-- Two external-separating cuts have the same source-side component block
exactly when they represent the same undirected graph edge.

The conclusion identifies *edges*, not pairing-leg representatives: the two
legs of one propagator represent the same cut. No external walk is chosen. -/
theorem TwoPointDiagram.externalSource_componentBlocks_eq_iff_edge_eq
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (cut₁ cut₂ : Fin (2 * (2 * S.card + 1)))
    (hsep₁ : ¬ (d.vertexGraphWithoutPropagator cut₁).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hsep₂ : ¬ (d.vertexGraphWithoutPropagator cut₂).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    (d.vertexGraphWithoutPropagator cut₁).componentBlock (Sum.inl (0 : Fin 2)) =
        (d.vertexGraphWithoutPropagator cut₂).componentBlock (Sum.inl (0 : Fin 2)) ↔
      s(twoPointVertexOfLeg cut₁, twoPointVertexOfLeg (d.pairing.partner cut₁)) =
        s(twoPointVertexOfLeg cut₂, twoPointVertexOfLeg (d.pairing.partner cut₂)) := by
  classical
  let s₀ : TwoPointVertex S := Sum.inl (0 : Fin 2)
  let t₁ : TwoPointVertex S := Sum.inl (1 : Fin 2)
  let H₁ := d.vertexGraphWithoutPropagator cut₁
  let H₂ := d.vertexGraphWithoutPropagator cut₂
  let e₁ : Sym2 (TwoPointVertex S) :=
    s(twoPointVertexOfLeg cut₁, twoPointVertexOfLeg (d.pairing.partner cut₁))
  let a : TwoPointVertex S := twoPointVertexOfLeg cut₂
  let b : TwoPointVertex S := twoPointVertexOfLeg (d.pairing.partner cut₂)
  let e₂ : Sym2 (TwoPointVertex S) := s(a, b)
  have hdel₁ : d.vertexGraph.deleteEdges {e₁} = H₁ :=
    d.deleteEdges_eq_vertexGraphWithoutPropagator_of_separatingCut hconnected cut₁ hsep₁
  have hdel₂ : d.vertexGraph.deleteEdges {e₂} = H₂ :=
    d.deleteEdges_eq_vertexGraphWithoutPropagator_of_separatingCut hconnected cut₂ hsep₂
  change H₁.componentBlock s₀ = H₂.componentBlock s₀ ↔ e₁ = e₂
  constructor
  · intro heq
    by_contra hne
    have hends := d.separatingCut_endpoints_not_reachable hconnected cut₂ hsep₂
    have hneEnds : a ≠ b := by
      intro hab
      exact hends (by simpa [hab] using
        (SimpleGraph.Reachable.refl a : H₂.Reachable a a))
    have hG : d.vertexGraph.Adj a b := ⟨hneEnds, cut₂, rfl, rfl⟩
    have hab : H₁.Adj a b := by
      rw [← hdel₁]
      apply (SimpleGraph.deleteEdges_adj).2
      refine ⟨hG, ?_⟩
      intro hbad
      exact hne (Set.mem_singleton_iff.mp hbad).symm
    have hreach (v : TwoPointVertex S) :
        H₁.Reachable s₀ v ↔ H₂.Reachable s₀ v := by
      constructor
      · intro hv
        have hm : v ∈ H₁.componentBlock s₀ :=
          (H₁.mem_componentBlock s₀ v).2 hv.symm
        rw [heq] at hm
        exact ((H₂.mem_componentBlock s₀ v).1 hm).symm
      · intro hv
        have hm : v ∈ H₂.componentBlock s₀ :=
          (H₂.mem_componentBlock s₀ v).2 hv.symm
        rw [← heq] at hm
        exact ((H₁.mem_componentBlock s₀ v).1 hm).symm
    rcases d.separatingCut_endpoints_opposite_sides hconnected cut₂ hsep₂ with
      ⟨ha, hb⟩ | ⟨hb, ha⟩
    · have hsa : H₁.Reachable s₀ a := (hreach a).2 ha
      have hsb : H₂.Reachable s₀ b :=
        (hreach b).1 (hsa.trans (SimpleGraph.Adj.reachable hab))
      exact hsep₂ (hsb.trans hb.symm)
    · have hsb : H₁.Reachable s₀ b := (hreach b).2 hb
      have hsa : H₂.Reachable s₀ a :=
        (hreach a).1 (hsb.trans (SimpleGraph.Adj.reachable hab.symm))
      exact hsep₂ (hsa.trans ha.symm)
  · intro heq
    have hgraph : H₁ = H₂ := by
      calc
        H₁ = d.vertexGraph.deleteEdges {e₁} := hdel₁.symm
        _ = d.vertexGraph.deleteEdges {e₂} := by rw [heq]
        _ = H₂ := hdel₂
    rw [hgraph]

/-- Distinct separating *edges* have strictly nested source-side components.
Thus inclusion gives a path-independent strict total comparison of the cut
edges, with the two legs of each propagator correctly identified. -/
theorem TwoPointDiagram.externalSource_componentBlocks_strict_comparable_of_edge_ne
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (cut₁ cut₂ : Fin (2 * (2 * S.card + 1)))
    (hsep₁ : ¬ (d.vertexGraphWithoutPropagator cut₁).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hsep₂ : ¬ (d.vertexGraphWithoutPropagator cut₂).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hne : s(twoPointVertexOfLeg cut₁, twoPointVertexOfLeg (d.pairing.partner cut₁)) ≠
      s(twoPointVertexOfLeg cut₂, twoPointVertexOfLeg (d.pairing.partner cut₂))) :
    (d.vertexGraphWithoutPropagator cut₁).componentBlock (Sum.inl (0 : Fin 2)) ⊂
      (d.vertexGraphWithoutPropagator cut₂).componentBlock (Sum.inl (0 : Fin 2)) ∨
    (d.vertexGraphWithoutPropagator cut₂).componentBlock (Sum.inl (0 : Fin 2)) ⊂
      (d.vertexGraphWithoutPropagator cut₁).componentBlock (Sum.inl (0 : Fin 2)) := by
  have hinj :=
    (d.externalSource_componentBlocks_eq_iff_edge_eq hconnected cut₁ cut₂ hsep₁ hsep₂).1
  rcases d.externalSource_componentBlocks_comparable hconnected cut₁ cut₂ hsep₁ hsep₂ with
    hsubset | hsubset
  · exact Or.inl (lt_of_le_of_ne hsubset (fun heq => hne (hinj heq)))
  · exact Or.inr (lt_of_le_of_ne hsubset (fun heq => hne (hinj heq.symm)))


end Common
end SecondQuantization
