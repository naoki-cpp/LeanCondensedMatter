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


/-- Distinct *undirected edges* represented by internal propagators that separate
the two external vertices. Image removes the duplication from choosing either leg of
a paired propagator. This is not a list of all graph bridges: only cuts separating the
distinguished external vertices are relevant to the 1PI chain. -/
noncomputable def TwoPointDiagram.separatingInternalEdges
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Finset (Sym2 (TwoPointVertex S)) := by
  classical
  exact ((Finset.univ : Finset (Fin (2 * (2 * S.card + 1)))).filter fun cut =>
    d.IsInternalPropagator cut ∧
      ¬ (d.vertexGraphWithoutPropagator cut).Reachable
        (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))).image fun cut =>
          s(twoPointVertexOfLeg cut, twoPointVertexOfLeg (d.pairing.partner cut))

/-- For a nontrivial connected two-point diagram, 1PI is exactly the absence of
internal separating edges. The finite family gives the cut-free criterion needed
for the eventual 1PI block reconstruction. -/
theorem TwoPointDiagram.isOneParticleIrreducible_iff_separatingInternalEdges_eq_empty
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.IsOneParticleIrreducible ↔
      S.Nonempty ∧ d.IsExternallyConnected ∧ d.separatingInternalEdges = ∅ := by
  classical
  constructor
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    ext e
    constructor
    · intro he
      rcases Finset.mem_image.mp he with ⟨cut, hcut, rfl⟩
      obtain ⟨hinternal, hsep⟩ := (Finset.mem_filter.mp hcut).2
      exact False.elim (hsep (h.2.2 cut hinternal))
    · simp
  · rintro ⟨hne, hconnected, hempty⟩
    refine ⟨hne, hconnected, ?_⟩
    intro cut hinternal
    by_contra hsep
    have hmem : s(twoPointVertexOfLeg cut,
        twoPointVertexOfLeg (d.pairing.partner cut)) ∈
        d.separatingInternalEdges := by
      apply Finset.mem_image.mpr
      refine ⟨cut, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hinternal, hsep⟩⟩
    rw [hempty] at hmem
    simpa using hmem

/-- Every internal edge that separates the two external vertices occurs on any
walk between them. In particular the set of separating edges does not depend on a
chosen path. -/
theorem TwoPointDiagram.separatingInternalEdges_subset_externalWalk_edges
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (p : d.vertexGraph.Walk (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (e : Sym2 (TwoPointVertex S))
    (he : e ∈ d.separatingInternalEdges) : e ∈ p.edges := by
  classical
  rcases Finset.mem_image.mp he with ⟨cut, hcut, rfl⟩
  have hsep := (Finset.mem_filter.mp hcut).2.2
  exact d.separatingCut_mem_edges_of_externalWalk hconnected cut hsep p

/-- The separating internal edges in their order along an external-to-external walk.
A trail or path supplies a list with no repeated edges; a general walk may repeat. -/
noncomputable def TwoPointDiagram.walkSeparatingInternalEdges
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (p : d.vertexGraph.Walk (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    List (Sym2 (TwoPointVertex S)) := by
  classical
  exact p.edges.filter fun e => e ∈ d.separatingInternalEdges

/-- The walk-ordered list contains exactly those edges that both occur on the walk
and separate the external vertices as internal propagators. -/
theorem TwoPointDiagram.mem_walkSeparatingInternalEdges_iff
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (p : d.vertexGraph.Walk (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (e : Sym2 (TwoPointVertex S)) :
    e ∈ d.walkSeparatingInternalEdges p ↔
      e ∈ p.edges ∧ e ∈ d.separatingInternalEdges := by
  classical
  simp [walkSeparatingInternalEdges]

/-- For any external-to-external walk, its filtered edge list enumerates *all*
separating internal edges, with no omissions or unrelated edges. -/
theorem TwoPointDiagram.walkSeparatingInternalEdges_toFinset
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (p : d.vertexGraph.Walk (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    (d.walkSeparatingInternalEdges p).toFinset = d.separatingInternalEdges := by
  classical
  ext e
  rw [List.mem_toFinset, d.mem_walkSeparatingInternalEdges_iff]
  exact ⟨And.right, fun he =>
    ⟨d.separatingInternalEdges_subset_externalWalk_edges hconnected p e he, he⟩⟩

/-- Along a trail, and hence along a path, every separating internal edge occurs
exactly once in the ordered list. -/
theorem TwoPointDiagram.walkSeparatingInternalEdges_nodup
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (p : d.vertexGraph.Walk (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hp : p.IsTrail) :
    (d.walkSeparatingInternalEdges p).Nodup := by
  classical
  unfold walkSeparatingInternalEdges
  exact hp.edges_nodup.filter _

/-- An externally connected two-point diagram admits an external path whose ordered
separating-edge list contains each separating internal edge exactly once.

This gives a finite linear enumeration, but not yet a proof that *its order* is
independent of the chosen external path. -/
theorem TwoPointDiagram.exists_path_enumerating_separatingInternalEdges
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected) :
    ∃ p : d.vertexGraph.Walk (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)),
      p.IsPath ∧
        (d.walkSeparatingInternalEdges p).Nodup ∧
        (d.walkSeparatingInternalEdges p).toFinset = d.separatingInternalEdges := by
  obtain ⟨p, hp⟩ := hconnected.2.exists_isPath
  exact ⟨p, hp, d.walkSeparatingInternalEdges_nodup p hp.isTrail,
    d.walkSeparatingInternalEdges_toFinset hconnected p⟩

end Common
end SecondQuantization
