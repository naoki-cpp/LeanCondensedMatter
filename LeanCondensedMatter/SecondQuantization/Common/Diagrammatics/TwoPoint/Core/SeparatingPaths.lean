import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.CutComponents

set_option linter.style.header false

/-!
# Separating propagators lie on every external path

The existing cut graph removes one *paired propagator*, retaining parallel lines. For a cut
separating the two external vertices in an externally connected two-point diagram, the cut
propagator is a bridge: there can be no surviving parallel line between its endpoints.

Consequently the cut graph equals Mathlib's `SimpleGraph.deleteEdges` of the underlying
undirected edge. This lets the existing graph-walk theorems establish that the edge occurs
in every walk between the two external vertices. The resulting path theorem is the first
step toward ordering all separating propagators into a chain of 1PI components.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S : Finset (Fin N)}

/-- For a separating cut of a connected two-point diagram, deleting the underlying
simple-graph edge is equivalent to deleting the specific paired propagator. This
fails without the separation hypothesis when other propagators share the same endpoints. -/
theorem TwoPointDiagram.deleteEdges_eq_vertexGraphWithoutPropagator_of_separatingCut
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (cut : Fin (2 * (2 * S.card + 1)))
    (hsep : ¬ (d.vertexGraphWithoutPropagator cut).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    d.vertexGraph.deleteEdges
        {s(twoPointVertexOfLeg cut, twoPointVertexOfLeg (d.pairing.partner cut))} =
      d.vertexGraphWithoutPropagator cut := by
  have hends :=
    d.separatingCut_endpoints_not_reachable hconnected cut hsep
  have hnot : ¬ (d.vertexGraphWithoutPropagator cut).Adj
      (twoPointVertexOfLeg cut) (twoPointVertexOfLeg (d.pairing.partner cut)) :=
    fun h => hends (SimpleGraph.Adj.reachable h)
  have hdel : (d.vertexGraphWithoutPropagator cut).deleteEdges
      {s(twoPointVertexOfLeg cut, twoPointVertexOfLeg (d.pairing.partner cut))} =
        d.vertexGraphWithoutPropagator cut := by
    apply (SimpleGraph.deleteEdges_eq_self).2
    apply Set.disjoint_singleton_right.mpr
    exact hnot
  rw [d.vertexGraph_eq_withoutPropagator_sup_edge cut,
    SimpleGraph.deleteEdges_sup, hdel,
    SimpleGraph.deleteEdges_edge (Set.mem_singleton _)]
  simp

/-- Every walk from external vertex zero to external vertex one must cross the
edge represented by a separating propagator. This is independent of the chosen
external path and hence can be used to order the separating edges along a path. -/
theorem TwoPointDiagram.separatingCut_mem_edges_of_externalWalk
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (cut : Fin (2 * (2 * S.card + 1)))
    (hsep : ¬ (d.vertexGraphWithoutPropagator cut).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (p : d.vertexGraph.Walk (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    s(twoPointVertexOfLeg cut, twoPointVertexOfLeg (d.pairing.partner cut)) ∈ p.edges := by
  apply p.mem_edges_of_not_reachable_deleteEdges
  rw [d.deleteEdges_eq_vertexGraphWithoutPropagator_of_separatingCut hconnected cut hsep]
  exact hsep

end Common
end SecondQuantization
