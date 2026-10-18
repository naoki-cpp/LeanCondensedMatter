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

end Common
end SecondQuantization
