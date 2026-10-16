import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.OneParticleIrreducible
import LeanCondensedMatter.Combinatorics.SimpleGraphComponentPartition
import Mathlib.Combinatorics.SimpleGraph.Operations

set_option linter.style.header false

/-!
# Connected components after cutting a two-point propagator

Removing one paired propagator preserves all the other propagators, including lines parallel to
the removed one. Every surviving paired line therefore lies entirely in a connected component of
the cut graph. When the cut separates the two external vertices, their cut-graph component blocks
are different and no surviving line can join these blocks.

Use the existing `SimpleGraph.componentBlock` API rather than a parallel diagram-specific
component type. These statements concern the combinatorics of a single cut; splitting the paired
diagram into properly relabelled 1PI blocks is a separate construction.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S : Finset (Fin N)}

/-- The original vertex graph is recovered by adjoining the edge underlying the removed
paired propagator. This equality retains any parallel propagators in the cut graph and lets
standard `SimpleGraph` edge-deletion and bridge theory be used downstream. -/
theorem TwoPointDiagram.vertexGraph_eq_withoutPropagator_sup_edge
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (cut : Fin (2 * (2 * S.card + 1))) :
    d.vertexGraph =
      d.vertexGraphWithoutPropagator cut ⊔
        SimpleGraph.edge (twoPointVertexOfLeg cut)
          (twoPointVertexOfLeg (d.pairing.partner cut)) := by
  apply SimpleGraph.ext
  funext v w
  apply propext
  simp only [SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hne, leg, hv, hw⟩
    by_cases hleg : leg = cut
    · right
      subst leg
      exact (SimpleGraph.edge_adj _ _ _ _).2
        ⟨Or.inl ⟨hv.symm, hw.symm⟩, hne⟩
    · by_cases hpartner : d.pairing.partner leg = cut
      · right
        have hlegEq : leg = d.pairing.partner cut := by
          calc
            leg = d.pairing.partner (d.pairing.partner leg) :=
              (d.pairing.partner_involutive leg).symm
            _ = d.pairing.partner cut := congrArg d.pairing.partner hpartner
        exact (SimpleGraph.edge_adj _ _ _ _).2
          ⟨Or.inr ⟨hv.symm.trans (congrArg twoPointVertexOfLeg hlegEq),
            hw.symm.trans (congrArg twoPointVertexOfLeg hpartner)⟩, hne⟩
      · left
        exact ⟨hne, leg, hleg, hpartner, hv, hw⟩
  · rintro (hremaining | hedge)
    · rcases hremaining with ⟨hne, leg, _, _, hv, hw⟩
      exact ⟨hne, leg, hv, hw⟩
    · obtain ⟨hh, hne⟩ := (SimpleGraph.edge_adj _ _ _ _).1 hedge
      rcases hh with ⟨hv, hw⟩ | ⟨hv, hw⟩
      · exact ⟨hne, cut, hv.symm, hw.symm⟩
      · refine ⟨hne, d.pairing.partner cut, hv.symm, ?_⟩
        rw [d.pairing.partner_involutive cut]
        exact hw.symm

/-- The endpoints of any surviving propagator remain connected after cutting another line. -/
theorem TwoPointDiagram.reachable_partner_withoutPropagator
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (cut leg : Fin (2 * (2 * S.card + 1)))
    (hleg : leg ≠ cut) (hpartner : d.pairing.partner leg ≠ cut) :
    (d.vertexGraphWithoutPropagator cut).Reachable
      (twoPointVertexOfLeg leg) (twoPointVertexOfLeg (d.pairing.partner leg)) := by
  by_cases h : twoPointVertexOfLeg leg =
      twoPointVertexOfLeg (d.pairing.partner leg)
  · rw [h]
  · exact SimpleGraph.Adj.reachable
      ⟨h, leg, hleg, hpartner, rfl, rfl⟩

/-- After removing one propagator, every other paired line stays within one component block. -/
theorem TwoPointDiagram.componentBlock_partner_withoutPropagator
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (cut leg : Fin (2 * (2 * S.card + 1)))
    (hleg : leg ≠ cut) (hpartner : d.pairing.partner leg ≠ cut) :
    (d.vertexGraphWithoutPropagator cut).componentBlock
        (twoPointVertexOfLeg leg) =
      (d.vertexGraphWithoutPropagator cut).componentBlock
        (twoPointVertexOfLeg (d.pairing.partner leg)) :=
  (d.vertexGraphWithoutPropagator cut).componentBlock_eq_of_reachable
    (d.reachable_partner_withoutPropagator cut leg hleg hpartner)

/-- No uncut propagator connects the two distinct external component blocks of a separating cut.

The hypotheses say that the first endpoint is on the side of external vertex zero and the
second endpoint is on the side of external vertex one. -/
theorem TwoPointDiagram.not_uncutPropagator_between_externalComponents
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (cut leg : Fin (2 * (2 * S.card + 1)))
    (hcut : ¬ (d.vertexGraphWithoutPropagator cut).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hleg : leg ≠ cut) (hpartner : d.pairing.partner leg ≠ cut) :
    ¬ (twoPointVertexOfLeg leg ∈
        (d.vertexGraphWithoutPropagator cut).componentBlock (Sum.inl (0 : Fin 2)) ∧
       twoPointVertexOfLeg (d.pairing.partner leg) ∈
        (d.vertexGraphWithoutPropagator cut).componentBlock (Sum.inl (1 : Fin 2))) := by
  rintro ⟨hleft, hright⟩
  have hl := (((d.vertexGraphWithoutPropagator cut).mem_componentBlock
    (Sum.inl (0 : Fin 2)) (twoPointVertexOfLeg leg)).1 hleft).symm
  have hr := ((d.vertexGraphWithoutPropagator cut).mem_componentBlock
    (Sum.inl (1 : Fin 2))
    (twoPointVertexOfLeg (d.pairing.partner leg))).1 hright
  exact hcut ((hl.trans
    (d.reachable_partner_withoutPropagator cut leg hleg hpartner)).trans hr)

end Common
end SecondQuantization
