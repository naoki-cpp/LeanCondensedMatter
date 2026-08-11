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

open Classical in
/-- The vertices lying outside the external component — every vacuum component at once.

`interactionPart` accepts an arbitrary vertex set, so this indexes the quartic diagram that the
vacuum legs will carry. -/
noncomputable def TwoPointDiagram.vacuumVertexSet {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) : Finset (TwoPointVertex S) :=
  Finset.univ \ (d.externalComponentPart : Finset (TwoPointVertex S))

theorem TwoPointDiagram.mem_vacuumVertexSet_iff {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (v : TwoPointVertex S) :
    v ∈ d.vacuumVertexSet ↔ v ∉ (d.externalComponentPart : Finset (TwoPointVertex S)) := by
  classical
  simp [TwoPointDiagram.vacuumVertexSet]

/-- A leg is a vacuum leg exactly when its incident vertex is a vacuum vertex. -/
theorem TwoPointDiagram.legIsVacuum_iff_vertex_mem_vacuumVertexSet {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : Fin (2 * (2 * S.card + 1))) :
    d.LegIsVacuum leg ↔ twoPointVertexOfLeg leg ∈ d.vacuumVertexSet :=
  (d.mem_vacuumVertexSet_iff _).symm

/-- Neither external vertex is a vacuum vertex. -/
theorem TwoPointDiagram.externalVertex_not_mem_vacuumVertexSet {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (e : Fin 2) :
    (Sum.inl e : TwoPointVertex S) ∉ d.vacuumVertexSet := by
  rw [d.mem_vacuumVertexSet_iff, not_not]
  exact d.externalVertex_mem_externalComponentPart e

/-- The partner permutation restricted to the vacuum legs.

Well defined by `legIsVacuum_partner_iff`: a contraction never joins a vacuum leg to a leg of the
external component. -/
noncomputable def TwoPointDiagram.vacuumPartner {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Equiv.Perm {leg : Fin (2 * (2 * S.card + 1)) // d.LegIsVacuum leg} :=
  d.pairing.partner.subtypePerm fun leg => d.legIsVacuum_partner_iff leg

/-- The restricted partner has the same underlying flattened leg as the ambient partner. -/
theorem TwoPointDiagram.vacuumPartner_val {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) // d.LegIsVacuum leg}) :
    (d.vacuumPartner leg : Fin (2 * (2 * S.card + 1))) = d.pairing.partner leg :=
  congrArg Subtype.val (Equiv.Perm.subtypePerm_apply _ _ leg)

/-- The vacuum partner remains an involution. -/
theorem TwoPointDiagram.vacuumPartner_involutive {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Function.Involutive d.vacuumPartner := fun leg => by
  apply Subtype.ext
  rw [d.vacuumPartner_val, d.vacuumPartner_val, d.pairing.partner_involutive]

/-- The vacuum partner has no fixed points. -/
theorem TwoPointDiagram.vacuumPartner_ne_self {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) // d.LegIsVacuum leg}) :
    d.vacuumPartner leg ≠ leg := fun h =>
  d.pairing.partner_ne_self leg (by rw [← d.vacuumPartner_val, h])

/-- Unflattened vacuum legs are exactly the four local legs of the vacuum interaction vertices.

Same shape as `vacuumLegDataEquiv`, but for the union of all vacuum components rather than one of
them: the external case is impossible because no external vertex is a vacuum vertex. -/
noncomputable def TwoPointDiagram.vacuumPartLegDataEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    {leg : TwoPointLeg S // twoPointLegVertex leg ∈ d.vacuumVertexSet} ≃
      ↥(TwoPointDiagram.interactionPart d.vacuumVertexSet) × Fin 4 where
  toFun leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e => exact False.elim (d.externalVertex_not_mem_vacuumVertexSet e hleg)
    | inr p =>
        exact (⟨p.1.1,
          (TwoPointDiagram.mem_interactionPart_subtype d.vacuumVertexSet p.1).2 hleg⟩, p.2)
  invFun p :=
    let v : ↥S :=
      ⟨p.1.1, TwoPointDiagram.interactionPart_subset d.vacuumVertexSet p.1.2⟩
    ⟨Sum.inr (v, p.2), by
      change (Sum.inr v : TwoPointVertex S) ∈ d.vacuumVertexSet
      exact (TwoPointDiagram.mem_interactionPart_subtype d.vacuumVertexSet v).1 p.1.2⟩
  left_inv leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e => exact False.elim (d.externalVertex_not_mem_vacuumVertexSet e hleg)
    | inr p =>
        rcases p with ⟨v, l⟩
        apply Subtype.ext
        rfl
  right_inv p := by
    rcases p with ⟨v, l⟩
    apply Prod.ext
    · exact Subtype.ext (by rfl)
    · rfl

/-- Flattening preserves the vacuum-leg predicate. -/
theorem TwoPointDiagram.legIsVacuum_iff_unflattened {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : Fin (2 * (2 * S.card + 1))) :
    d.LegIsVacuum leg ↔ twoPointLegVertex (twoPointLegEquiv S leg) ∈ d.vacuumVertexSet := by
  rw [d.legIsVacuum_iff_vertex_mem_vacuumVertexSet]

/-- Reindex the vacuum legs as the flattened legs of an ordinary quartic diagram. -/
noncomputable def TwoPointDiagram.vacuumPartBlockLegEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    {leg : Fin (2 * (2 * S.card + 1)) // d.LegIsVacuum leg} ≃
      Fin (2 * (2 * (TwoPointDiagram.interactionPart d.vacuumVertexSet).card)) :=
  ((twoPointLegEquiv S).subtypeEquiv fun leg => d.legIsVacuum_iff_unflattened leg).trans
    (d.vacuumPartLegDataEquiv.trans
      (quarticLegEquiv (TwoPointDiagram.interactionPart d.vacuumVertexSet)).symm)

private theorem vacuumPermCongr_involutive {α β : Type*} (e : α ≃ β)
    (p : Equiv.Perm α) (hp : Function.Involutive p) :
    Function.Involutive (e.permCongr p) := by
  intro x
  simp [Equiv.permCongr_apply, hp (e.symm x)]

private theorem vacuumPermCongr_ne_self {α β : Type*} (e : α ≃ β)
    (p : Equiv.Perm α) (hp : ∀ x, p x ≠ x) (x : β) :
    e.permCongr p x ≠ x := by
  intro h
  rw [Equiv.permCongr_apply, Equiv.apply_eq_iff_eq_symm_apply] at h
  exact hp _ h

/-- The perfect pairing carried by the vacuum legs. -/
noncomputable def TwoPointDiagram.vacuumPartPairing {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Pairing (2 * (TwoPointDiagram.interactionPart d.vacuumVertexSet).card) :=
  Pairing.ofPartner
    (d.vacuumPartBlockLegEquiv.permCongr d.vacuumPartner)
    ⟨vacuumPermCongr_involutive _ _ d.vacuumPartner_involutive,
      vacuumPermCongr_ne_self _ _ d.vacuumPartner_ne_self⟩

/-- The vacuum pairing agrees with the ambient partner under the vacuum leg reindexing. -/
theorem TwoPointDiagram.vacuumPartPairing_partner_vacuumPartBlockLegEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) // d.LegIsVacuum leg}) :
    d.vacuumPartPairing.partner (d.vacuumPartBlockLegEquiv leg) =
      d.vacuumPartBlockLegEquiv (d.vacuumPartner leg) := by
  simp [TwoPointDiagram.vacuumPartPairing, Pairing.ofPartner, Equiv.permCongr_apply]

/-- **The vacuum part of a two-point diagram as a single quartic diagram.** Unlike
`restrictVacuumComponent` this collects every vacuum component at once, so the result is in general
disconnected — which is exactly what the binary external/vacuum factorization consumes. -/
noncomputable def TwoPointDiagram.restrictVacuumPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    QuarticDiagram InternalLabel N (TwoPointDiagram.interactionPart d.vacuumVertexSet) where
  vertexLabel v :=
    d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset d.vacuumVertexSet v.2⟩
  pairing := d.vacuumPartPairing

@[simp]
theorem TwoPointDiagram.restrictVacuumPart_pairing {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.restrictVacuumPart.pairing = d.vacuumPartPairing :=
  rfl

end Common
end SecondQuantization
