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

end Common
end SecondQuantization
