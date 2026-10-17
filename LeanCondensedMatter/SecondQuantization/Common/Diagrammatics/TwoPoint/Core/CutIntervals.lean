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
    · rw [d.pairing.partner_involutive leg]
      exact he
    · rw [d.pairing.partner_involutive leg]
      exact hl
  · rintro ⟨hmem, hpe, he', hpl, hl'⟩
    have he : leg ≠ earlier := by
      rw [d.pairing.partner_involutive leg] at he'
      exact he'
    have hl : leg ≠ later := by
      rw [d.pairing.partner_involutive leg] at hl'
      exact hl'
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


/-- For the later of two nested cuts, exactly one paired endpoint lies inside
the interval: the endpoint on its source-external side. The cut is represented
by either of its paired legs, with no choice of an external walk. -/
theorem TwoPointDiagram.laterCut_endpoints_opposite_interval_sides
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hnested :
      (d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2)) ⊆
        (d.vertexGraphWithoutPropagator later).componentBlock (Sum.inl (0 : Fin 2)))
    (hsep : ¬ (d.vertexGraphWithoutPropagator later).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hne : later ≠ earlier)
    (hpne : d.pairing.partner later ≠ earlier) :
    (twoPointVertexOfLeg later ∈ d.verticesBetweenCuts earlier later ∧
        twoPointVertexOfLeg (d.pairing.partner later) ∉
          d.verticesBetweenCuts earlier later) ∨
      (twoPointVertexOfLeg (d.pairing.partner later) ∈
          d.verticesBetweenCuts earlier later ∧
        twoPointVertexOfLeg later ∉ d.verticesBetweenCuts earlier later) := by
  let H := d.vertexGraphWithoutPropagator later
  let s₀ : TwoPointVertex S := Sum.inl (0 : Fin 2)
  let t₁ : TwoPointVertex S := Sum.inl (1 : Fin 2)
  let a := twoPointVertexOfLeg later
  let b := twoPointVertexOfLeg (d.pairing.partner later)
  have hinvariant := sourceSide_mem_partner_iff d earlier later hne hpne
  have hnotTarget {v : TwoPointVertex S}
      (hv : H.Reachable t₁ v) :
      v ∉ H.componentBlock s₀ := by
    intro hmem
    have hsource : H.Reachable s₀ v :=
      ((H.mem_componentBlock s₀ v).1 hmem).symm
    exact hsep (hsource.trans hv.symm)
  rcases d.separatingCut_endpoints_opposite_sides hconnected later hsep with
    ⟨ha, hb⟩ | ⟨hb, ha⟩
  · left
    have hasource : a ∈ H.componentBlock s₀ :=
      (H.mem_componentBlock s₀ a).2 ha.symm
    have hnotb : b ∉ H.componentBlock s₀ := hnotTarget hb
    have hnota : a ∉
        (d.vertexGraphWithoutPropagator earlier).componentBlock s₀ := by
      intro hmem
      exact hnotb (hnested (hinvariant.mp hmem))
    exact ⟨(d.mem_verticesBetweenCuts_iff earlier later a).2
      ⟨hasource, hnota⟩,
      fun h => hnotb ((d.mem_verticesBetweenCuts_iff earlier later b).1 h).1⟩
  · right
    have hbsource : b ∈ H.componentBlock s₀ :=
      (H.mem_componentBlock s₀ b).2 hb.symm
    have hnota : a ∉ H.componentBlock s₀ := hnotTarget ha
    have hnotb : b ∉
        (d.vertexGraphWithoutPropagator earlier).componentBlock s₀ := by
      intro hmem
      exact hnota (hnested (hinvariant.mpr hmem))
    exact ⟨(d.mem_verticesBetweenCuts_iff earlier later b).2
      ⟨hbsource, hnotb⟩,
      fun h => hnota ((d.mem_verticesBetweenCuts_iff earlier later a).1 h).1⟩

/-- The earlier separating cut also has exactly one endpoint in the interval:
the endpoint on the target-external side of that cut.

The nesting condition makes the earlier propagator survive the later cut and
therefore keeps its two endpoints on the same later source side. -/
theorem TwoPointDiagram.earlierCut_endpoints_opposite_interval_sides
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hnested :
      (d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2)) ⊆
        (d.vertexGraphWithoutPropagator later).componentBlock (Sum.inl (0 : Fin 2)))
    (hsep : ¬ (d.vertexGraphWithoutPropagator earlier).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hne : earlier ≠ later)
    (hpne : d.pairing.partner earlier ≠ later) :
    (twoPointVertexOfLeg earlier ∈ d.verticesBetweenCuts earlier later ∧
        twoPointVertexOfLeg (d.pairing.partner earlier) ∉
          d.verticesBetweenCuts earlier later) ∨
      (twoPointVertexOfLeg (d.pairing.partner earlier) ∈
          d.verticesBetweenCuts earlier later ∧
        twoPointVertexOfLeg earlier ∉ d.verticesBetweenCuts earlier later) := by
  let H := d.vertexGraphWithoutPropagator earlier
  let K := d.vertexGraphWithoutPropagator later
  let s₀ : TwoPointVertex S := Sum.inl (0 : Fin 2)
  let t₁ : TwoPointVertex S := Sum.inl (1 : Fin 2)
  let a := twoPointVertexOfLeg earlier
  let b := twoPointVertexOfLeg (d.pairing.partner earlier)
  have hinvariant := sourceSide_mem_partner_iff d later earlier hne hpne
  have hnotTarget {v : TwoPointVertex S}
      (hv : H.Reachable t₁ v) :
      v ∉ H.componentBlock s₀ := by
    intro hmem
    have hsource : H.Reachable s₀ v :=
      ((H.mem_componentBlock s₀ v).1 hmem).symm
    exact hsep (hsource.trans hv.symm)
  rcases d.separatingCut_endpoints_opposite_sides hconnected earlier hsep with
    ⟨ha, hb⟩ | ⟨hb, ha⟩
  · right
    have hasource : a ∈ H.componentBlock s₀ :=
      (H.mem_componentBlock s₀ a).2 ha.symm
    have hbsource : b ∈ K.componentBlock s₀ :=
      hinvariant.mp (hnested hasource)
    have hnotb : b ∉ H.componentBlock s₀ := hnotTarget hb
    exact ⟨(d.mem_verticesBetweenCuts_iff earlier later b).2
      ⟨hbsource, hnotb⟩,
      fun h => ((d.mem_verticesBetweenCuts_iff earlier later a).1 h).2 hasource⟩
  · left
    have hbsource : b ∈ H.componentBlock s₀ :=
      (H.mem_componentBlock s₀ b).2 hb.symm
    have hasource : a ∈ K.componentBlock s₀ :=
      hinvariant.mpr (hnested hbsource)
    have hnota : a ∉ H.componentBlock s₀ := hnotTarget ha
    exact ⟨(d.mem_verticesBetweenCuts_iff earlier later a).2
      ⟨hasource, hnota⟩,
      fun h => ((d.mem_verticesBetweenCuts_iff earlier later b).1 h).2 hbsource⟩

/-- Choose the interval-facing leg of a paired cut by membership in the
canonical intermediate vertex region, rather than by a path orientation.
For a boundary cut, the previous lemmas show that the choice is unique. -/
noncomputable def TwoPointDiagram.intervalFacingLeg
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later cut : Fin (2 * (2 * S.card + 1))) :
    Fin (2 * (2 * S.card + 1)) := by
  classical
  exact if twoPointVertexOfLeg cut ∈ d.verticesBetweenCuts earlier later
    then cut else d.pairing.partner cut

/-- Exactly one of the two endpoints of a cut lies in the interval if and only
if the selected interval-facing leg is inside and its partner is outside. -/
theorem TwoPointDiagram.intervalFacingLeg_mem_and_partner_not_mem
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later cut : Fin (2 * (2 * S.card + 1)))
    (hends :
      (twoPointVertexOfLeg cut ∈ d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg (d.pairing.partner cut) ∉
            d.verticesBetweenCuts earlier later) ∨
        (twoPointVertexOfLeg (d.pairing.partner cut) ∈
            d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg cut ∉ d.verticesBetweenCuts earlier later)) :
    twoPointVertexOfLeg (d.intervalFacingLeg earlier later cut) ∈
        d.verticesBetweenCuts earlier later ∧
      twoPointVertexOfLeg (d.pairing.partner (d.intervalFacingLeg earlier later cut)) ∉
        d.verticesBetweenCuts earlier later := by
  classical
  unfold TwoPointDiagram.intervalFacingLeg
  split_ifs with h
  · rcases hends with ⟨_, hout⟩ | ⟨_, hout⟩
    · exact ⟨h, hout⟩
    · exact False.elim (hout h)
  · rcases hends with ⟨hin, _⟩ | ⟨hin, hout⟩
    · exact False.elim (h hin)
    · rw [d.pairing.partner_involutive cut]
      exact ⟨hin, hout⟩

/-- The interval-facing representative of a propagator is always one of its
two paired legs. -/
theorem TwoPointDiagram.intervalFacingLeg_eq_cut_or_partner
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later cut : Fin (2 * (2 * S.card + 1))) :
    d.intervalFacingLeg earlier later cut = cut ∨
      d.intervalFacingLeg earlier later cut = d.pairing.partner cut := by
  classical
  unfold TwoPointDiagram.intervalFacingLeg
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- For a boundary propagator with exactly one endpoint in the interval,
the facing leg is independent of which paired leg names that propagator. -/
theorem TwoPointDiagram.intervalFacingLeg_partner
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later cut : Fin (2 * (2 * S.card + 1)))
    (hends :
      (twoPointVertexOfLeg cut ∈ d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg (d.pairing.partner cut) ∉
            d.verticesBetweenCuts earlier later) ∨
        (twoPointVertexOfLeg (d.pairing.partner cut) ∈
            d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg cut ∉ d.verticesBetweenCuts earlier later)) :
    d.intervalFacingLeg earlier later (d.pairing.partner cut) =
      d.intervalFacingLeg earlier later cut := by
  classical
  unfold TwoPointDiagram.intervalFacingLeg
  rcases hends with ⟨hin, hout⟩ | ⟨hin, hout⟩
  · simp [hin, hout]
  · simp [hin, hout]

/-- A leg of a boundary propagator belonging to the interval is necessarily
the canonical interval-facing representative. -/
theorem TwoPointDiagram.intervalBoundaryLeg_eq_facing
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later cut leg : Fin (2 * (2 * S.card + 1)))
    (hends :
      (twoPointVertexOfLeg cut ∈ d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg (d.pairing.partner cut) ∉
            d.verticesBetweenCuts earlier later) ∨
        (twoPointVertexOfLeg (d.pairing.partner cut) ∈
            d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg cut ∉ d.verticesBetweenCuts earlier later))
    (hpair : leg = cut ∨ leg = d.pairing.partner cut)
    (hmem : twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later) :
    leg = d.intervalFacingLeg earlier later cut := by
  classical
  rcases hpair with rfl | rfl
  · simp [TwoPointDiagram.intervalFacingLeg, hmem]
  · have hnot : twoPointVertexOfLeg cut ∉ d.verticesBetweenCuts earlier later := by
      rcases hends with ⟨_, hout⟩ | ⟨_, hout⟩
      · exact False.elim (hout hmem)
      · exact hout
    simp [TwoPointDiagram.intervalFacingLeg, hnot]

/-- Every leg incident to the interval is either paired to another interior
leg or is one of the two uniquely identified, interval-facing boundary legs.
This is an exhaustive partition at the level of ambient flattened legs,
before replacing the boundary propagators with new external legs. -/
theorem TwoPointDiagram.mem_verticesBetweenCuts_iff_interior_or_boundary
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later leg : Fin (2 * (2 * S.card + 1)))
    (hEarlier :
      (twoPointVertexOfLeg earlier ∈ d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg (d.pairing.partner earlier) ∉
            d.verticesBetweenCuts earlier later) ∨
        (twoPointVertexOfLeg (d.pairing.partner earlier) ∈
            d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg earlier ∉ d.verticesBetweenCuts earlier later))
    (hLater :
      (twoPointVertexOfLeg later ∈ d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg (d.pairing.partner later) ∉
            d.verticesBetweenCuts earlier later) ∨
        (twoPointVertexOfLeg (d.pairing.partner later) ∈
            d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg later ∉ d.verticesBetweenCuts earlier later)) :
    twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later ↔
      d.IsInteriorLeg earlier later leg ∨
        leg = d.intervalFacingLeg earlier later earlier ∨
        leg = d.intervalFacingLeg earlier later later := by
  classical
  constructor
  · intro hmem
    by_cases he : leg = earlier
    · exact Or.inr (Or.inl
        (d.intervalBoundaryLeg_eq_facing earlier later earlier leg hEarlier
          (Or.inl he) hmem))
    by_cases hpe : d.pairing.partner leg = earlier
    · have hleg : leg = d.pairing.partner earlier := by
        calc
          leg = d.pairing.partner (d.pairing.partner leg) :=
            (d.pairing.partner_involutive leg).symm
          _ = d.pairing.partner earlier := congrArg d.pairing.partner hpe
      exact Or.inr (Or.inl
        (d.intervalBoundaryLeg_eq_facing earlier later earlier leg hEarlier
          (Or.inr hleg) hmem))
    by_cases hl : leg = later
    · exact Or.inr (Or.inr
        (d.intervalBoundaryLeg_eq_facing earlier later later leg hLater
          (Or.inl hl) hmem))
    by_cases hpl : d.pairing.partner leg = later
    · have hleg : leg = d.pairing.partner later := by
        calc
          leg = d.pairing.partner (d.pairing.partner leg) :=
            (d.pairing.partner_involutive leg).symm
          _ = d.pairing.partner later := congrArg d.pairing.partner hpl
      exact Or.inr (Or.inr
        (d.intervalBoundaryLeg_eq_facing earlier later later leg hLater
          (Or.inr hleg) hmem))
    exact Or.inl ⟨hmem, he, hpe, hl, hpl⟩
  · rintro (hinterior | hleft | hright)
    · exact hinterior.1
    · rw [hleft]
      exact (d.intervalFacingLeg_mem_and_partner_not_mem earlier later earlier hEarlier).1
    · rw [hright]
      exact (d.intervalFacingLeg_mem_and_partner_not_mem earlier later later hLater).1

/-- Facing legs for different paired boundary propagators are different.
Unlike comparing raw cut legs, this also covers either representative of
each cut. -/
theorem TwoPointDiagram.intervalFacingLeg_ne_of_pair_ne
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hne : earlier ≠ later)
    (hpne : d.pairing.partner earlier ≠ later) :
    d.intervalFacingLeg earlier later earlier ≠
      d.intervalFacingLeg earlier later later := by
  intro h
  rcases d.intervalFacingLeg_eq_cut_or_partner earlier later earlier with ha | ha
  · rcases d.intervalFacingLeg_eq_cut_or_partner earlier later later with hb | hb
    · exact hne (ha.symm.trans (h.trans hb))
    · have h' : earlier = d.pairing.partner later :=
        ha.symm.trans (h.trans hb)
      apply hpne
      exact (congrArg d.pairing.partner h').trans
        (d.pairing.partner_involutive later)
  · rcases d.intervalFacingLeg_eq_cut_or_partner earlier later later with hb | hb
    · exact hpne (ha.symm.trans (h.trans hb))
    · exact hne (d.pairing.partner.injective (ha.symm.trans (h.trans hb)))

/-- Interior legs cannot coincide with either boundary-facing representative.
This is the disjointness complement to the exhaustive interval-leg classification. -/
theorem TwoPointDiagram.isInteriorLeg_ne_intervalFacingLeg
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later cut leg : Fin (2 * (2 * S.card + 1)))
    (hcut : cut = earlier ∨ cut = later)
    (hinterior : d.IsInteriorLeg earlier later leg) :
    leg ≠ d.intervalFacingLeg earlier later cut := by
  intro heq
  rcases hinterior with ⟨_, he, hpe, hl, hpl⟩
  rcases d.intervalFacingLeg_eq_cut_or_partner earlier later cut with hf | hf
  · rcases hcut with rfl | rfl
    · exact he (heq.trans hf)
    · exact hl (heq.trans hf)
  · have hp : d.pairing.partner leg = cut := by
      rw [heq, hf, d.pairing.partner_involutive cut]
    rcases hcut with rfl | rfl
    · exact hpe hp
    · exact hpl hp

/-- The legs incident to a cut interval split as a disjoint union of all
uncut interior legs and the two facing boundary legs. This finite-set
identity is the domain decomposition needed to insert replacement external
legs and transport the pairing to a standard two-point leg space. -/
open Classical in
theorem TwoPointDiagram.intervalIncidentLegs_eq_interior_union_boundary
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hEarlier :
      (twoPointVertexOfLeg earlier ∈ d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg (d.pairing.partner earlier) ∉
            d.verticesBetweenCuts earlier later) ∨
        (twoPointVertexOfLeg (d.pairing.partner earlier) ∈
            d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg earlier ∉ d.verticesBetweenCuts earlier later))
    (hLater :
      (twoPointVertexOfLeg later ∈ d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg (d.pairing.partner later) ∉
            d.verticesBetweenCuts earlier later) ∨
        (twoPointVertexOfLeg (d.pairing.partner later) ∈
            d.verticesBetweenCuts earlier later ∧
          twoPointVertexOfLeg later ∉ d.verticesBetweenCuts earlier later)) :
    ((Finset.univ : Finset (Fin (2 * (2 * S.card + 1)))).filter
        (fun leg => twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later)) =
      ((Finset.univ : Finset (Fin (2 * (2 * S.card + 1)))).filter
        (d.IsInteriorLeg earlier later)) ∪
          {d.intervalFacingLeg earlier later earlier,
           d.intervalFacingLeg earlier later later} := by
  classical
  ext leg
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] using
    (d.mem_verticesBetweenCuts_iff_interior_or_boundary earlier later leg hEarlier hLater)

end Common
end SecondQuantization
