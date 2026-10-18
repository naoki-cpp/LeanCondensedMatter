import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.IntervalPairing

set_option linter.style.header false

/-!
# Connectivity of cut-interval blocks

The two replacement external vertices of an interval block are each
attached to an interaction vertex. The full external connectivity and
1PI statements require further graph-level arguments.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S : Finset (Fin N)}

/-- Each replacement external vertex is adjacent to an interaction vertex
in the standalone interval block, not to the other external vertex. -/
theorem TwoPointDiagram.intervalBlock_external_adjacent_interaction
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (boundaryLabels : Fin 2 → ExternalLabel)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hsepLater : ¬ (d.vertexGraphWithoutPropagator later).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hEarlier : d.HasIntervalBoundaryEndpoint earlier later earlier)
    (hLater : d.HasIntervalBoundaryEndpoint earlier later later)
    (hne : earlier ≠ later)
    (hpne : d.pairing.partner earlier ≠ later)
    (i : Fin 2) :
    ∃ v : ↥(interactionSector (d.verticesBetweenCuts earlier later)),
      (d.intervalBlock boundaryLabels earlier later hsepLater
        hEarlier hLater hne hpne).vertexGraph.Adj (Sum.inl i) (Sum.inr v) := by
  let T := interactionSector (d.verticesBetweenCuts earlier later)
  let b := d.intervalBlock boundaryLabels earlier later hsepLater hEarlier hLater hne hpne
  let p : Fin (2 * (2 * T.card + 1)) :=
    b.pairing.partner (twoPointExternalLeg T i)
  have hp :
      (d.intervalBlockLegEquiv earlier later hsepLater) p =
        Sum.inr ((d.intervalBoundaryInteriorLegEquiv earlier later
          hEarlier hLater hne hpne) (Sum.inl i)) :=
    d.intervalBlock_partner_external boundaryLabels earlier later
      hsepLater hEarlier hLater hne hpne i
  cases hz : twoPointLegEquiv T p with
  | inl j =>
      have hj :
          (d.intervalBlockLegEquiv earlier later hsepLater) p = Sum.inl j := by
        simp [TwoPointDiagram.intervalBlockLegEquiv, T, hz]
      rw [hj] at hp
      cases hp
  | inr vl =>
      refine ⟨vl.1, ?_⟩
      change (b.pairing.vertexGraph twoPointVertexOfLeg).Adj
        (Sum.inl i) (Sum.inr vl.1)
      refine ⟨by simp, twoPointExternalLeg T i, ?_, ?_⟩
      · exact twoPointVertexOfLeg_externalLeg T i
      · change twoPointVertexOfLeg p = Sum.inr vl.1
        simp [twoPointVertexOfLeg, hz]


/-- An ambient interior propagator between two interval interaction slots
remains a propagator between the corresponding vertices of the reconstructed
block. The original partner is transported, not recomputed. -/
theorem TwoPointDiagram.intervalBlock_adj_interaction_of_interior_partner
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (boundaryLabels : Fin 2 → ExternalLabel)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hsepLater : ¬ (d.vertexGraphWithoutPropagator later).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hEarlier : d.HasIntervalBoundaryEndpoint earlier later earlier)
    (hLater : d.HasIntervalBoundaryEndpoint earlier later later)
    (hne : earlier ≠ later)
    (hpne : d.pairing.partner earlier ≠ later)
    (v w : ↥(interactionSector (d.verticesBetweenCuts earlier later)))
    (lv lw : Fin 4)
    (hvw : v ≠ w)
    (hinterior : d.IsInteriorLeg earlier later
      ((d.intervalInteractionLegEquiv earlier later hsepLater) (v, lv)).1)
    (hpartner : d.pairing.partner
      ((d.intervalInteractionLegEquiv earlier later hsepLater) (v, lv)).1 =
        ((d.intervalInteractionLegEquiv earlier later hsepLater) (w, lw)).1) :
    (d.intervalBlock boundaryLabels earlier later hsepLater
      hEarlier hLater hne hpne).vertexGraph.Adj (Sum.inr v) (Sum.inr w) := by
  let E := d.intervalBlockLegEquiv earlier later hsepLater
  let I := d.intervalInteractionLegEquiv earlier later hsepLater
  let b := d.intervalBlock boundaryLabels earlier later
    hsepLater hEarlier hLater hne hpne
  let i : {leg : Fin (2 * (2 * S.card + 1)) //
      d.IsInteriorLeg earlier later leg} := ⟨(I (v, lv)).1, hinterior⟩
  have hev : E (twoPointInteractionLeg v lv) =
      Sum.inr (⟨i.1, i.2.1⟩ : {leg : Fin (2 * (2 * S.card + 1)) //
        twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later}) := by
    simpa only [i] using
      (d.intervalBlockLegEquiv_interaction earlier later hsepLater v lv)
  have hsrc : E.symm (Sum.inr (⟨i.1, i.2.1⟩ :
        {leg : Fin (2 * (2 * S.card + 1)) //
          twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later})) =
      twoPointInteractionLeg v lv :=
    E.injective (by simpa only [Equiv.apply_symm_apply] using hev.symm)
  have hp : E (b.pairing.partner (twoPointInteractionLeg v lv)) =
      Sum.inr (⟨d.pairing.partner i.1,
        ((d.isInteriorLeg_partner_iff earlier later i.1).mp i.2).1⟩ :
          {leg : Fin (2 * (2 * S.card + 1)) //
            twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later}) := by
    rw [← hsrc]
    exact d.intervalBlock_partner_interior_ambient boundaryLabels earlier later
      hsepLater hEarlier hLater hne hpne i
  have hew : E (twoPointInteractionLeg w lw) =
      Sum.inr (⟨d.pairing.partner i.1,
        ((d.isInteriorLeg_partner_iff earlier later i.1).mp i.2).1⟩ :
          {leg : Fin (2 * (2 * S.card + 1)) //
            twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later}) := by
    rw [d.intervalBlockLegEquiv_interaction earlier later hsepLater w lw]
    exact congrArg Sum.inr (Subtype.ext (by simpa only [i] using hpartner.symm))
  have hpblock : b.pairing.partner (twoPointInteractionLeg v lv) =
      twoPointInteractionLeg w lw := E.injective (hp.trans hew.symm)
  change (b.pairing.vertexGraph twoPointVertexOfLeg).Adj (Sum.inr v) (Sum.inr w)
  exact ⟨fun h => hvw (Sum.inr.inj h), twoPointInteractionLeg v lv,
    twoPointVertexOfLeg_interactionLeg v lv,
    by rw [hpblock]; exact twoPointVertexOfLeg_interactionLeg w lw⟩

/-- On vertices of a cut interval, deleting either (or both) boundary
propagators does not change adjacency. Each boundary propagator has
exactly one endpoint in the interval, so neither can join two vertices
of the interval. -/
theorem TwoPointDiagram.intervalVertices_doubleCut_adj_iff
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hEarlier : d.HasIntervalBoundaryEndpoint earlier later earlier)
    (hLater : d.HasIntervalBoundaryEndpoint earlier later later)
    (u v : TwoPointVertex S)
    (hu : u ∈ d.verticesBetweenCuts earlier later)
    (hv : v ∈ d.verticesBetweenCuts earlier later) :
    (d.vertexGraphWithoutPropagator earlier ⊓
      d.vertexGraphWithoutPropagator later).Adj u v ↔
        d.vertexGraph.Adj u v := by
  constructor
  · intro h
    change (d.vertexGraphWithoutPropagator earlier).Adj u v ∧
      (d.vertexGraphWithoutPropagator later).Adj u v at h
    exact d.vertexGraphWithoutPropagator_le_vertexGraph earlier h.1
  · rintro ⟨hne, leg, hleg, hpartner⟩
    have hlegMem : twoPointVertexOfLeg leg ∈
        d.verticesBetweenCuts earlier later := by
      simpa only [hleg] using hu
    have hpartnerMem : twoPointVertexOfLeg (d.pairing.partner leg) ∈
        d.verticesBetweenCuts earlier later := by
      simpa only [hpartner] using hv
    have admissible (cut : Fin (2 * (2 * S.card + 1)))
        (hcut : d.HasIntervalBoundaryEndpoint earlier later cut) :
        leg ≠ cut ∧ d.pairing.partner leg ≠ cut := by
      have hnotBoth :
          ¬ (twoPointVertexOfLeg cut ∈ d.verticesBetweenCuts earlier later ∧
            twoPointVertexOfLeg (d.pairing.partner cut) ∈
              d.verticesBetweenCuts earlier later) := by
        rintro ⟨hc, hpc⟩
        rcases hcut with ⟨_, hout⟩ | ⟨_, hout⟩
        · exact hout hpc
        · exact hout hc
      constructor
      · intro h
        subst leg
        exact hnotBoth ⟨hlegMem, hpartnerMem⟩
      · intro h
        apply hnotBoth
        constructor
        · rw [← h]
          exact hpartnerMem
        · have hp : d.pairing.partner cut = leg := by
            calc
              d.pairing.partner cut =
                  d.pairing.partner (d.pairing.partner leg) :=
                    congrArg d.pairing.partner h.symm
              _ = leg := d.pairing.partner_involutive leg
          rw [hp]
          exact hlegMem
    obtain ⟨he, hpe⟩ := admissible earlier hEarlier
    obtain ⟨hl, hpl⟩ := admissible later hLater
    change (d.vertexGraphWithoutPropagator earlier).Adj u v ∧
      (d.vertexGraphWithoutPropagator later).Adj u v
    exact ⟨⟨hne, leg, he, hpe, hleg, hpartner⟩,
      ⟨hne, leg, hl, hpl, hleg, hpartner⟩⟩

/-- As graphs on the interval's own vertex subtype, removing both
boundary propagators changes nothing: the induced double-cut graph
equals the graph induced from the original diagram. In particular,
any interval-confined path can be used unchanged after both cuts. -/
theorem TwoPointDiagram.intervalVertices_induce_doubleCut_eq
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hEarlier : d.HasIntervalBoundaryEndpoint earlier later earlier)
    (hLater : d.HasIntervalBoundaryEndpoint earlier later later) :
    SimpleGraph.induce
        (↑(d.verticesBetweenCuts earlier later) : Set (TwoPointVertex S))
        (d.vertexGraphWithoutPropagator earlier ⊓
          d.vertexGraphWithoutPropagator later) =
      SimpleGraph.induce
        (↑(d.verticesBetweenCuts earlier later) : Set (TwoPointVertex S))
        d.vertexGraph := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  simpa only [SimpleGraph.induce_adj] using
    (d.intervalVertices_doubleCut_adj_iff earlier later hEarlier hLater
      u.1 v.1 u.2 v.2)

/-- The ambient graph induced on a strictly nested cut interval is
connected. The interval is one component after the two cuts are removed,
and Mathlib's induced graph on a connected component is connected. -/
theorem TwoPointDiagram.intervalVertices_induced_connected
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hstrict :
      (d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2)) ⊂
        (d.vertexGraphWithoutPropagator later).componentBlock (Sum.inl (0 : Fin 2)))
    (hsepEarlier : ¬ (d.vertexGraphWithoutPropagator earlier).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hsepLater : ¬ (d.vertexGraphWithoutPropagator later).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hEarlier : d.HasIntervalBoundaryEndpoint earlier later earlier)
    (hLater : d.HasIntervalBoundaryEndpoint earlier later later) :
    (SimpleGraph.induce
      (↑(d.verticesBetweenCuts earlier later) : Set (TwoPointVertex S))
      d.vertexGraph).Connected := by
  classical
  obtain ⟨u, hu⟩ : (d.verticesBetweenCuts earlier later).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr
      (d.verticesBetweenCuts_ne_empty_of_ssubset earlier later hstrict)
  let G := d.vertexGraphWithoutPropagator earlier ⊓
    d.vertexGraphWithoutPropagator later
  let C := G.connectedComponentMk u
  have hC : C.supp =
      (↑(d.verticesBetweenCuts earlier later) : Set (TwoPointVertex S)) := by
    ext v
    change G.connectedComponentMk v = G.connectedComponentMk u ↔
      v ∈ d.verticesBetweenCuts earlier later
    rw [SimpleGraph.ConnectedComponent.eq,
      ← d.doubleCut_componentBlock_eq_verticesBetweenCuts
        hconnected earlier later hsepEarlier hsepLater u hu]
    exact (G.mem_componentBlock u v).symm
  have hc : (SimpleGraph.induce C.supp G).Connected :=
    C.connected_toSimpleGraph
  rw [hC] at hc
  rw [← d.intervalVertices_induce_doubleCut_eq
    earlier later hEarlier hLater]
  exact hc

end Common
end SecondQuantization
