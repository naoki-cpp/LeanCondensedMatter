import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.CutOrder

set_option linter.style.header false

/-!
# Vertex intervals between separating propagators

For two ordered external-separating cuts, the difference of their source-side
component blocks is the finite region between those cuts. It is a nonempty
region whenever the source-side inclusion is strict.

Most importantly, all propagators other than the two boundary cuts preserve
membership in this region. This establishes the closure needed to restrict
the ambient pairing to each eventual 1PI block, once the boundary lines have
been turned into external legs. The present module does not yet perform that
relabeling or claim the resulting diagram is 1PI.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S : Finset (Fin N)}

/-- Vertices between two cuts: the source component of the later cut minus
the source component of the earlier cut. When the cuts are not ordered this
difference still makes sense, but it need not be a nonempty interval. -/
noncomputable def TwoPointDiagram.verticesBetweenCuts
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1))) :
    Finset (TwoPointVertex S) := by
  classical
  exact (d.vertexGraphWithoutPropagator later).componentBlock (Sum.inl (0 : Fin 2)) \
    (d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2))

/-- Membership in the intermediate region is characterized by the two
canonical source-side component blocks. -/
theorem TwoPointDiagram.mem_verticesBetweenCuts_iff
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (v : TwoPointVertex S) :
    v ∈ d.verticesBetweenCuts earlier later ↔
      v ∈ (d.vertexGraphWithoutPropagator later).componentBlock (Sum.inl (0 : Fin 2)) ∧
      v ∉ (d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2)) := by
  classical
  simp [verticesBetweenCuts]

/-- A strictly ordered pair of separating cuts leaves at least one vertex
between them. No arbitrary external path is involved. -/
theorem TwoPointDiagram.verticesBetweenCuts_ne_empty_of_ssubset
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hstrict :
      (d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2)) ⊂
        (d.vertexGraphWithoutPropagator later).componentBlock (Sum.inl (0 : Fin 2))) :
    d.verticesBetweenCuts earlier later ≠ ∅ := by
  classical
  intro hempty
  have hreverse :
      (d.vertexGraphWithoutPropagator later).componentBlock (Sum.inl (0 : Fin 2)) ⊆
        (d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2)) := by
    intro v hv
    by_contra hnot
    have hmem : v ∈ d.verticesBetweenCuts earlier later :=
      (d.mem_verticesBetweenCuts_iff earlier later v).2 ⟨hv, hnot⟩
    rw [hempty] at hmem
    simp at hmem
  exact (not_le_of_gt hstrict) hreverse

/-- For nested cut sides, the later source side is partitioned into the
earlier source side and the intervening vertex region. -/
theorem TwoPointDiagram.sourceSide_union_verticesBetweenCuts
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hsubset :
      (d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2)) ⊆
        (d.vertexGraphWithoutPropagator later).componentBlock (Sum.inl (0 : Fin 2))) :
    (d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2)) ∪
        d.verticesBetweenCuts earlier later =
      (d.vertexGraphWithoutPropagator later).componentBlock (Sum.inl (0 : Fin 2)) := by
  classical
  ext v
  rw [Finset.mem_union, d.mem_verticesBetweenCuts_iff]
  constructor
  · rintro (hl | ⟨hr, _⟩)
    · exact hsubset hl
    · exact hr
  · intro hr
    by_cases hl : v ∈
        (d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2))
    · exact Or.inl hl
    · exact Or.inr ⟨hr, hl⟩

/-- The interval is disjoint from the earlier source component. -/
theorem TwoPointDiagram.verticesBetweenCuts_disjoint_earlier
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1))) :
    Disjoint
      ((d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2)))
      (d.verticesBetweenCuts earlier later) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hleft hmid
  exact ((d.mem_verticesBetweenCuts_iff earlier later v).1 hmid).2 hleft

/-- A paired propagator surviving a cut preserves source-side membership.
This is local proof infrastructure, rather than a second public component API. -/
private theorem sourceSide_mem_partner_iff
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (cut leg : Fin (2 * (2 * S.card + 1)))
    (hleg : leg ≠ cut) (hpartner : d.pairing.partner leg ≠ cut) :
    twoPointVertexOfLeg leg ∈
        (d.vertexGraphWithoutPropagator cut).componentBlock (Sum.inl (0 : Fin 2)) ↔
      twoPointVertexOfLeg (d.pairing.partner leg) ∈
        (d.vertexGraphWithoutPropagator cut).componentBlock (Sum.inl (0 : Fin 2)) := by
  let H := d.vertexGraphWithoutPropagator cut
  let root : TwoPointVertex S := Sum.inl (0 : Fin 2)
  have hlink : H.Reachable (twoPointVertexOfLeg leg)
      (twoPointVertexOfLeg (d.pairing.partner leg)) :=
    d.reachable_partner_withoutPropagator cut leg hleg hpartner
  constructor
  · intro hm
    apply (H.mem_componentBlock root (twoPointVertexOfLeg (d.pairing.partner leg))).2
    exact hlink.symm.trans ((H.mem_componentBlock root (twoPointVertexOfLeg leg)).1 hm)
  · intro hm
    apply (H.mem_componentBlock root (twoPointVertexOfLeg leg)).2
    exact hlink.trans
      ((H.mem_componentBlock root (twoPointVertexOfLeg (d.pairing.partner leg))).1 hm)

/-- Except for either boundary propagator, both endpoints of a paired line
lie in the intermediate region together or outside it together.

This is the pairing-closure statement required for extracting a two-point
block from the interval: no uncut pairing crosses its vertex boundary. -/
theorem TwoPointDiagram.verticesBetweenCuts_partner_iff
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later leg : Fin (2 * (2 * S.card + 1)))
    (hEarlier : leg ≠ earlier)
    (hpEarlier : d.pairing.partner leg ≠ earlier)
    (hLater : leg ≠ later)
    (hpLater : d.pairing.partner leg ≠ later) :
    twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later ↔
      twoPointVertexOfLeg (d.pairing.partner leg) ∈
        d.verticesBetweenCuts earlier later := by
  classical
  have hearlier := sourceSide_mem_partner_iff d earlier leg hEarlier hpEarlier
  have hlater := sourceSide_mem_partner_iff d later leg hLater hpLater
  simp only [d.mem_verticesBetweenCuts_iff, hlater, hearlier]

end Common
end SecondQuantization
