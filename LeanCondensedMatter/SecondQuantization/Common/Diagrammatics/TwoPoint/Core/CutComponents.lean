import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.OneParticleIrreducible
import LeanCondensedMatter.Combinatorics.SimpleGraphComponentPartition

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

/-- A propagator separating the external vertices puts them into different cut-graph blocks. -/
theorem TwoPointDiagram.externalComponentBlocks_ne_withoutPropagator
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (cut : Fin (2 * (2 * S.card + 1)))
    (hcut : ¬ (d.vertexGraphWithoutPropagator cut).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    (d.vertexGraphWithoutPropagator cut).componentBlock
        (Sum.inl (0 : Fin 2)) ≠
      (d.vertexGraphWithoutPropagator cut).componentBlock
        (Sum.inl (1 : Fin 2)) := by
  intro heq
  exact hcut (((d.vertexGraphWithoutPropagator cut).componentBlock_eq_iff_reachable
    (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))).1 heq)

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

/-- The cut-graph connected-component partition does not depend on the endpoint used to name
the removed paired propagator. -/
theorem TwoPointDiagram.componentBlock_withoutPropagator_partner_cut
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (cut : Fin (2 * (2 * S.card + 1)))
    (v : TwoPointVertex S) :
    (d.vertexGraphWithoutPropagator (d.pairing.partner cut)).componentBlock v =
      (d.vertexGraphWithoutPropagator cut).componentBlock v := by
  rw [d.vertexGraphWithoutPropagator_partner]

end Common
end SecondQuantization
