import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.CutOrder
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.InteractionSector

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


/-- The source external vertex lies outside every intermediate region. -/
theorem TwoPointDiagram.externalZero_not_mem_verticesBetweenCuts
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1))) :
    (Sum.inl (0 : Fin 2) : TwoPointVertex S) ∉
      d.verticesBetweenCuts earlier later := by
  intro h
  exact ((d.mem_verticesBetweenCuts_iff earlier later _).1 h).2
    ((d.vertexGraphWithoutPropagator earlier).self_mem_componentBlock _)

/-- If the later cut separates the external vertices, the target external
vertex is outside the intermediate region as well. -/
theorem TwoPointDiagram.externalOne_not_mem_verticesBetweenCuts
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hsep : ¬ (d.vertexGraphWithoutPropagator later).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    (Sum.inl (1 : Fin 2) : TwoPointVertex S) ∉
      d.verticesBetweenCuts earlier later := by
  intro h
  have hmem := ((d.mem_verticesBetweenCuts_iff earlier later _).1 h).1
  exact hsep (((d.vertexGraphWithoutPropagator later).mem_componentBlock
    (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))).1 hmem).symm

/-- The interaction vertices between two cuts are the existing generic
interaction-sector extraction of their intermediate vertex region. -/
theorem TwoPointDiagram.mem_interactionSector_verticesBetweenCuts_iff
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1))) (v : ↥S) :
    (v : Fin N) ∈ interactionSector (d.verticesBetweenCuts earlier later) ↔
      (Sum.inr v : TwoPointVertex S) ∈ d.verticesBetweenCuts earlier later :=
  mem_interactionSector_subtype (d.verticesBetweenCuts earlier later) v

/-- Between two strictly nested external-separating cuts there is at least
one interaction vertex. This is the nontriviality requirement for an eventual
proper 1PI two-point block. -/
theorem TwoPointDiagram.interactionSector_verticesBetweenCuts_nonempty
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hstrict :
      (d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2)) ⊂
        (d.vertexGraphWithoutPropagator later).componentBlock (Sum.inl (0 : Fin 2)))
    (hsep : ¬ (d.vertexGraphWithoutPropagator later).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    (interactionSector (d.verticesBetweenCuts earlier later)).Nonempty := by
  classical
  have hne := d.verticesBetweenCuts_ne_empty_of_ssubset earlier later hstrict
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  cases v with
  | inl e =>
      fin_cases e
      · exact False.elim (d.externalZero_not_mem_verticesBetweenCuts earlier later hv)
      · exact False.elim
          (d.externalOne_not_mem_verticesBetweenCuts earlier later hsep hv)
  | inr v =>
      exact ⟨v.1, (d.mem_interactionSector_verticesBetweenCuts_iff earlier later v).2 hv⟩

/-- A leg strictly inside the interval, excluding both paired boundary
propagators. Each excluded cut is removed together with its partner, not
merely its chosen representative leg. -/
def TwoPointDiagram.IsInteriorLeg
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later leg : Fin (2 * (2 * S.card + 1))) : Prop :=
  twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later ∧
    leg ≠ earlier ∧ d.pairing.partner leg ≠ earlier ∧
    leg ≠ later ∧ d.pairing.partner leg ≠ later

/-- The uncut interior legs form a partner-invariant subtype. -/
theorem TwoPointDiagram.isInteriorLeg_partner_iff
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later leg : Fin (2 * (2 * S.card + 1))) :
    d.IsInteriorLeg earlier later leg ↔
      d.IsInteriorLeg earlier later (d.pairing.partner leg) := by
  constructor
  · rintro ⟨hmem, he, hpe, hl, hpl⟩
    have hmem' :=
      (d.verticesBetweenCuts_partner_iff earlier later leg he hpe hl hpl).1 hmem
    refine ⟨hmem', hpe, ?_, hpl, ?_⟩
    · simpa only [d.pairing.partner_involutive] using he
    · simpa only [d.pairing.partner_involutive] using hl
  · rintro ⟨hmem, hpe, he', hpl, hl'⟩
    have he : leg ≠ earlier := by
      simpa only [d.pairing.partner_involutive] using he'
    have hl : leg ≠ later := by
      simpa only [d.pairing.partner_involutive] using hl'
    exact ⟨(d.verticesBetweenCuts_partner_iff earlier later leg he hpe hl hpl).2
      (by simpa only [d.pairing.partner_involutive] using hmem),
      he, hpe, hl, hpl⟩

/-- The ambient perfect pairing, restricted to uncut legs of the interval.

The two boundary lines are deliberately excluded. Their interior endpoints
will be paired with newly inserted external legs when a standalone two-point
block is constructed. -/
noncomputable def TwoPointDiagram.interiorPairing
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1))) :
    Combinatorics.PairingOn
      {leg : Fin (2 * (2 * S.card + 1)) // d.IsInteriorLeg earlier later leg} :=
  d.pairing.restrict (d.IsInteriorLeg earlier later)
    (d.isInteriorLeg_partner_iff earlier later)

/-- Restricting to the interval leaves the partner of every interior leg
unchanged as an ambient flattened leg. -/
theorem TwoPointDiagram.interiorPairing_partner_val
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (leg : {leg : Fin (2 * (2 * S.card + 1)) // d.IsInteriorLeg earlier later leg}) :
    ((d.interiorPairing earlier later).partner leg :
      {leg : Fin (2 * (2 * S.card + 1)) // d.IsInteriorLeg earlier later leg}).1 =
        d.pairing.partner leg := by
  simpa only [TwoPointDiagram.interiorPairing] using
    d.pairing.restrict_partner_val (d.IsInteriorLeg earlier later)
      (d.isInteriorLeg_partner_iff earlier later) leg

end Common
end SecondQuantization
