import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.SeparatingPaths
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalConnectivity

set_option linter.style.header false

/-!
# The two sides of a separating propagator

A connected two-point diagram has exactly two cut-graph components after an
external-separating propagator is removed. They are canonically distinguished by
the external vertices, without selecting an external walk or orienting the cut line.

The graph-theoretic ingredient is that if adjoining one edge makes a graph
preconnected, then every vertex is reachable from at least one endpoint of that edge.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S : Finset (Fin N)}

/-- If a walk from `x` to `a` uses edges of a graph together with the one
edge `a-b`, then `x` was already connected to `a` or `b` in the original graph. -/
private theorem reachable_one_endpoint_of_reachable_sup_edge
    {V : Type*} (G : SimpleGraph V) (a b x : V)
    (h : (G ⊔ SimpleGraph.edge a b).Reachable x a) :
    G.Reachable x a ∨ G.Reachable x b := by
  refine h.elim ?_
  intro p
  induction p with
  | nil =>
      exact Or.inl (SimpleGraph.Reachable.refl _)
  | @cons u v w huv p ih =>
      have htail : G.Reachable v a ∨ G.Reachable v b := ih p.reachable
      rcases (SimpleGraph.sup_adj G (SimpleGraph.edge a b) u v).1 huv with hG | hedge
      · rcases htail with ha | hb
        · exact Or.inl ((SimpleGraph.Adj.reachable hG).trans ha)
        · exact Or.inr ((SimpleGraph.Adj.reachable hG).trans hb)
      · rcases ((SimpleGraph.edge_adj a b u v).1 hedge).1 with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (SimpleGraph.Reachable.refl _)
        · exact Or.inr (SimpleGraph.Reachable.refl _)

/-- Every vertex of an externally connected two-point diagram belongs to one of
the two external connected components after a separating propagator is cut.

Together with the separation hypothesis, this proves that the cut graph has
exactly two components. The result includes the interaction vertices, so it
rules out a third disconnected component becoming isolated by this cut. -/
theorem TwoPointDiagram.reachable_external_side_withoutPropagator
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (cut : Fin (2 * (2 * S.card + 1)))
    (hsep : ¬ (d.vertexGraphWithoutPropagator cut).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (v : TwoPointVertex S) :
    (d.vertexGraphWithoutPropagator cut).Reachable (Sum.inl (0 : Fin 2)) v ∨
      (d.vertexGraphWithoutPropagator cut).Reachable (Sum.inl (1 : Fin 2)) v := by
  let H := d.vertexGraphWithoutPropagator cut
  let a := twoPointVertexOfLeg cut
  let b := twoPointVertexOfLeg (d.pairing.partner cut)
  have hpre : d.vertexGraph.Preconnected :=
    (d.preconnected_iff_isExternallyConnected).2 hconnected
  have hgraph : d.vertexGraph = H ⊔ SimpleGraph.edge a b :=
    d.vertexGraph_eq_withoutPropagator_sup_edge cut
  have hends (w : TwoPointVertex S) : H.Reachable w a ∨ H.Reachable w b := by
    have hw : d.vertexGraph.Reachable w a := hpre w a
    rw [hgraph] at hw
    exact reachable_one_endpoint_of_reachable_sup_edge H a b w hw
  rcases hends (Sum.inl (0 : Fin 2)) with h0a | h0b
  · rcases hends (Sum.inl (1 : Fin 2)) with h1a | h1b
    · exact False.elim (hsep (h0a.trans h1a.symm))
    · rcases hends v with hva | hvb
      · exact Or.inl (h0a.trans hva.symm)
      · exact Or.inr (h1b.trans hvb.symm)
  · rcases hends (Sum.inl (1 : Fin 2)) with h1a | h1b
    · rcases hends v with hva | hvb
      · exact Or.inr (h1a.trans hva.symm)
      · exact Or.inl (h0b.trans hvb.symm)
    · exact False.elim (hsep (h0b.trans h1b.symm))

/-- The removed propagator joins the two *different* canonical external sides of
the cut, in one of its two orientations. No choice of representative leg is made
by the conclusion. -/
theorem TwoPointDiagram.separatingCut_endpoints_opposite_sides
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (cut : Fin (2 * (2 * S.card + 1)))
    (hsep : ¬ (d.vertexGraphWithoutPropagator cut).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    ((d.vertexGraphWithoutPropagator cut).Reachable
        (Sum.inl (0 : Fin 2)) (twoPointVertexOfLeg cut) ∧
      (d.vertexGraphWithoutPropagator cut).Reachable
        (Sum.inl (1 : Fin 2)) (twoPointVertexOfLeg (d.pairing.partner cut))) ∨
    ((d.vertexGraphWithoutPropagator cut).Reachable
        (Sum.inl (0 : Fin 2)) (twoPointVertexOfLeg (d.pairing.partner cut)) ∧
      (d.vertexGraphWithoutPropagator cut).Reachable
        (Sum.inl (1 : Fin 2)) (twoPointVertexOfLeg cut)) := by
  have hends := d.separatingCut_endpoints_not_reachable hconnected cut hsep
  rcases d.reachable_external_side_withoutPropagator hconnected cut hsep
      (twoPointVertexOfLeg cut) with h0a | h1a
  · rcases d.reachable_external_side_withoutPropagator hconnected cut hsep
        (twoPointVertexOfLeg (d.pairing.partner cut)) with h0b | h1b
    · exact False.elim (hends (h0a.symm.trans h0b))
    · exact Or.inl ⟨h0a, h1b⟩
  · rcases d.reachable_external_side_withoutPropagator hconnected cut hsep
        (twoPointVertexOfLeg (d.pairing.partner cut)) with h0b | h1b
    · exact Or.inr ⟨h0b, h1a⟩
    · exact False.elim (hends (h1a.symm.trans h1b))

/-- The two canonical external component blocks cover the whole vertex set and are disjoint.
Consequently a separating cut has *exactly* two connected components. -/
theorem TwoPointDiagram.external_componentBlocks_cover_and_disjoint
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (cut : Fin (2 * (2 * S.card + 1)))
    (hsep : ¬ (d.vertexGraphWithoutPropagator cut).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    (d.vertexGraphWithoutPropagator cut).componentBlock (Sum.inl (0 : Fin 2)) ∪
      (d.vertexGraphWithoutPropagator cut).componentBlock (Sum.inl (1 : Fin 2)) =
        (Finset.univ : Finset (TwoPointVertex S)) ∧
    Disjoint
      ((d.vertexGraphWithoutPropagator cut).componentBlock (Sum.inl (0 : Fin 2)))
      ((d.vertexGraphWithoutPropagator cut).componentBlock (Sum.inl (1 : Fin 2))) := by
  classical
  constructor
  · ext v
    constructor
    · intro _
      exact Finset.mem_univ v
    · intro _
      rcases d.reachable_external_side_withoutPropagator hconnected cut hsep v with h0 | h1
      · exact Finset.mem_union.mpr (Or.inl
          (((d.vertexGraphWithoutPropagator cut).mem_componentBlock
            (Sum.inl (0 : Fin 2)) v).2 h0.symm))
      · exact Finset.mem_union.mpr (Or.inr
          (((d.vertexGraphWithoutPropagator cut).mem_componentBlock
            (Sum.inl (1 : Fin 2)) v).2 h1.symm))
  · apply Finset.disjoint_left.mpr
    intro v h0 h1
    have hreach0 :=
      (((d.vertexGraphWithoutPropagator cut).mem_componentBlock
        (Sum.inl (0 : Fin 2)) v).1 h0).symm
    have hreach1 :=
      ((d.vertexGraphWithoutPropagator cut).mem_componentBlock
        (Sum.inl (1 : Fin 2)) v).1 h1
    exact hsep (hreach0.trans hreach1)

end Common
end SecondQuantization
