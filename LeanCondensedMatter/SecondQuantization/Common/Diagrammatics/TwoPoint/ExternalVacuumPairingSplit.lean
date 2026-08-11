import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.VacuumLeg

set_option linter.style.header false

/-!
# The pairing of a two-point diagram splits into its external and vacuum pairings

`TwoPointDiagram.legPositionSplitting` presents the ambient legs as the external component's legs
together with the vacuum legs. This module records what the diagram's own pairing does under that
presentation: it is exactly `Pairing.ofSplit` applied to the two restricted pairings, so nothing is
lost by taking a two-point diagram apart along the external/vacuum divide.

Together with `Pairing.splitEquiv` this is the pairing half of the binary decomposition. The vertex
labels are the other half, and they need no theory: each vertex lies on exactly one side.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- The left part of the leg splitting is the external component's legs, unchanged as ambient
legs. -/
@[simp]
theorem TwoPointDiagram.legPositionSplitting_inl {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (i : Fin (2 * (2 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card + 1))) :
    d.legPositionSplitting (Sum.inl i) =
      (d.externalBlockLegEquiv.symm i : Fin (2 * (2 * S.card + 1))) :=
  rfl

/-- The right part of the leg splitting is the vacuum legs, unchanged as ambient legs. -/
@[simp]
theorem TwoPointDiagram.legPositionSplitting_inr {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (j : Fin (2 * (2 * (TwoPointDiagram.interactionPart d.vacuumVertexSet).card))) :
    d.legPositionSplitting (Sum.inr j) =
      (d.vacuumPartBlockLegEquiv.symm j : Fin (2 * (2 * S.card + 1))) :=
  rfl

/-- The external leg reindexing intertwines the restricted external pairing with the ambient
partner. -/
theorem TwoPointDiagram.externalBlockLegEquiv_symm_restrictedExternalPairing_partner
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (i : Fin (2 * (2 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card + 1))) :
    d.externalBlockLegEquiv.symm (d.restrictedExternalPairing.partner i) =
      d.restrictedPartner (d.externalComponent 0) (d.externalBlockLegEquiv.symm i) := by
  rw [Equiv.symm_apply_eq]
  have h := d.restrictedExternalPairing_partner_externalBlockLegEquiv
    (d.externalBlockLegEquiv.symm i)
  rwa [Equiv.apply_symm_apply] at h

/-- The vacuum leg reindexing intertwines the vacuum pairing with the ambient partner. -/
theorem TwoPointDiagram.vacuumPartBlockLegEquiv_symm_vacuumPartPairing_partner
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (j : Fin (2 * (2 * (TwoPointDiagram.interactionPart d.vacuumVertexSet).card))) :
    d.vacuumPartBlockLegEquiv.symm (d.vacuumPartPairing.partner j) =
      d.vacuumPartner (d.vacuumPartBlockLegEquiv.symm j) := by
  rw [Equiv.symm_apply_eq]
  have h := d.vacuumPartPairing_partner_vacuumPartBlockLegEquiv
    (d.vacuumPartBlockLegEquiv.symm j)
  rwa [Equiv.apply_symm_apply] at h

/-- **The pairing of a two-point diagram is assembled from its external and vacuum pairings.**

No contraction joins the external component to a vacuum component, so the ambient partner map is the
two restricted partner maps run side by side along `legPositionSplitting`. -/
theorem TwoPointDiagram.ofSplit_legPositionSplitting_eq_pairing {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Pairing.ofSplit d.legPositionSplitting d.restrictedExternalPairing d.vacuumPartPairing =
      d.pairing := by
  refine Pairing.ext (Equiv.ext fun leg => ?_)
  obtain ⟨x, rfl⟩ := d.legPositionSplitting.surjective leg
  cases x with
  | inl i =>
      rw [Pairing.ofSplit_partner_inl, d.legPositionSplitting_inl, d.legPositionSplitting_inl,
        ← d.restrictedPartner_val (d.externalComponent 0) (d.externalBlockLegEquiv.symm i)]
      exact congrArg Subtype.val
        (d.externalBlockLegEquiv_symm_restrictedExternalPairing_partner i)
  | inr j =>
      rw [Pairing.ofSplit_partner_inr, d.legPositionSplitting_inr, d.legPositionSplitting_inr,
        ← d.vacuumPartner_val (d.vacuumPartBlockLegEquiv.symm j)]
      exact congrArg Subtype.val
        (d.vacuumPartBlockLegEquiv_symm_vacuumPartPairing_partner j)

/-- **The pairing is split by the external/vacuum leg splitting.** -/
theorem TwoPointDiagram.isSplit_legPositionSplitting {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.pairing.IsSplit d.legPositionSplitting := by
  rw [← d.ofSplit_legPositionSplitting_eq_pairing]
  exact Pairing.isSplit_ofSplit _ _ _

/-- Restricting the ambient pairing to the left part returns the external component's pairing. -/
theorem TwoPointDiagram.splitLeft_legPositionSplitting {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (h : d.pairing.IsSplit d.legPositionSplitting) :
    d.pairing.splitLeft d.legPositionSplitting h = d.restrictedExternalPairing := by
  refine Pairing.ext (Equiv.ext fun i => ?_)
  have h1 := Pairing.partner_splitLeft d.legPositionSplitting h i
  have h2 : d.pairing.partner (d.legPositionSplitting (Sum.inl i)) =
      d.legPositionSplitting (Sum.inl (d.restrictedExternalPairing.partner i)) := by
    rw [← d.ofSplit_legPositionSplitting_eq_pairing, Pairing.ofSplit_partner_inl]
  exact Sum.inl.inj (d.legPositionSplitting.injective (h1.symm.trans h2))

/-- Restricting the ambient pairing to the right part returns the vacuum pairing. -/
theorem TwoPointDiagram.splitRight_legPositionSplitting {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (h : d.pairing.IsSplit d.legPositionSplitting) :
    d.pairing.splitRight d.legPositionSplitting h = d.vacuumPartPairing := by
  refine Pairing.ext (Equiv.ext fun j => ?_)
  have h1 := Pairing.partner_splitRight d.legPositionSplitting h j
  have h2 : d.pairing.partner (d.legPositionSplitting (Sum.inr j)) =
      d.legPositionSplitting (Sum.inr (d.vacuumPartPairing.partner j)) := by
    rw [← d.ofSplit_legPositionSplitting_eq_pairing, Pairing.ofSplit_partner_inr]
  exact Sum.inr.inj (d.legPositionSplitting.injective (h1.symm.trans h2))

end Common
end SecondQuantization
