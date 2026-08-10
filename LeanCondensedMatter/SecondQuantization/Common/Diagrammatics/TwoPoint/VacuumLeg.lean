import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentRestriction

set_option linter.style.header false

/-!
# The vacuum legs of a two-point diagram

A flattened leg is a *vacuum leg* when its incident vertex lies outside the component carrying the
two external vertices. This is the complement of one part, not a single part, so it is coarser than
`TwoPointDiagram.legInComponent`: it collects **all** vacuum components at once.

That coarser predicate is what a binary external/vacuum split needs. The connected-component
decomposition of a two-point diagram is used only through the statement that exactly one component
meets the external vertices, so the diagram splits in two: the external connected piece and one
possibly disconnected vacuum piece.

The three facts recorded here are the hypotheses every later construction consumes: vacuum legs are
closed under the pairing partner, the external legs are not vacuum, and a leg is vacuum exactly when
its component is one of the vacuum parts.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- A flattened leg is a **vacuum leg** when its incident vertex lies outside the external
component. -/
def TwoPointDiagram.LegIsVacuum {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : Fin (2 * (2 * S.card + 1))) : Prop :=
  twoPointVertexOfLeg leg ∉ (d.externalComponentPart : Finset (TwoPointVertex S))

/-- Being a vacuum leg is membership-in-the-external-component, negated. -/
theorem TwoPointDiagram.legIsVacuum_iff_not_legInComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : Fin (2 * (2 * S.card + 1))) :
    d.LegIsVacuum leg ↔
      ¬ d.legInComponent (d.externalComponentPart : Finset (TwoPointVertex S)) leg := by
  rw [TwoPointDiagram.LegIsVacuum,
    d.legInComponent_iff_vertex_mem d.externalComponentPart.2 leg]

/-- **Vacuum legs are closed under the pairing.** A contraction never joins a vacuum leg to an
external-component leg. -/
theorem TwoPointDiagram.legIsVacuum_partner_iff {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : Fin (2 * (2 * S.card + 1))) :
    d.LegIsVacuum (d.pairing.partner leg) ↔ d.LegIsVacuum leg := by
  simp only [d.legIsVacuum_iff_not_legInComponent, not_iff_not]
  exact (d.legInComponent_partner_iff
    (d.externalComponentPart : Finset (TwoPointVertex S)) leg).symm

/-- The partner of a vacuum leg is a vacuum leg. -/
theorem TwoPointDiagram.legIsVacuum_partner {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    {leg : Fin (2 * (2 * S.card + 1))} (h : d.LegIsVacuum leg) :
    d.LegIsVacuum (d.pairing.partner leg) :=
  (d.legIsVacuum_partner_iff leg).2 h

/-- **External legs are never vacuum legs.** -/
theorem TwoPointDiagram.not_legIsVacuum_of_vertex_external {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    {leg : Fin (2 * (2 * S.card + 1))} {e : Fin 2}
    (h : twoPointVertexOfLeg leg = (Sum.inl e : TwoPointVertex S)) :
    ¬ d.LegIsVacuum leg := by
  rw [TwoPointDiagram.LegIsVacuum, h, not_not]
  exact d.externalVertex_mem_externalComponentPart e

/-- **A leg is vacuum exactly when its component is a vacuum part.** This is the bridge between the
binary external/vacuum split used by the linked-cluster factorization and the component-indexed
statements of `ComponentDecomposition`. -/
theorem TwoPointDiagram.legIsVacuum_iff_exists_vacuumComponentPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : Fin (2 * (2 * S.card + 1))) :
    d.LegIsVacuum leg ↔
      ∃ B : d.componentPartition.parts, B ∈ d.vacuumComponentParts ∧
        d.legInComponent (B : Finset (TwoPointVertex S)) leg := by
  constructor
  · intro h
    refine ⟨⟨d.componentBlock (twoPointVertexOfLeg leg),
      d.componentBlock_mem_componentPartition _⟩, ?_, rfl⟩
    rw [d.mem_vacuumComponentParts, d.componentIsVacuum_iff_ne_externalComponentPart]
    intro hEq
    exact h (((d.componentBlock_eq_iff_mem d.externalComponentPart.2 _).1
      (congrArg Subtype.val hEq)))
  · rintro ⟨B, hB, hleg⟩ hmem
    rw [d.mem_vacuumComponentParts, d.componentIsVacuum_iff_ne_externalComponentPart] at hB
    refine hB (Subtype.ext ?_)
    rw [← hleg]
    exact (d.componentBlock_eq_iff_mem d.externalComponentPart.2 _).2 hmem

end Common
end SecondQuantization
