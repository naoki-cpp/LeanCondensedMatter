import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Restricting a pairing to an invariant subtype

A `PairingOn α` can be restricted to any partner-invariant predicate on `α`. The restricted
fixed-point-free involution is itself a pairing on the invariant subtype, and an arbitrary
equivalence may then transport it to any target type.

The ordered finite `Pairing n` inherits this construction directly. Diagrammatic users remain
responsible only for the invariant predicate and their domain-specific reindexing equivalence.
-/

namespace Combinatorics

/-- Restrict the partner permutation of a pairing to a partner-invariant subtype. -/
noncomputable def Pairing.partnerSubtypePerm {α : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i)) :
    Equiv.Perm {i : α // p i} :=
  pairing.partner.subtypePerm fun i => (hpartner i).symm

@[simp]
theorem Pairing.partnerSubtypePerm_val {α : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (i : {i : α // p i}) :
    ((pairing.partnerSubtypePerm p hpartner i : {i : α // p i}) : α) =
      pairing.partner i :=
  congrArg Subtype.val (Equiv.Perm.subtypePerm_apply _ _ i)

private theorem Pairing.partnerSubtypePerm_involutive {α : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i)) :
    Function.Involutive (pairing.partnerSubtypePerm p hpartner) := fun i => by
  apply Subtype.ext
  rw [pairing.partnerSubtypePerm_val, pairing.partnerSubtypePerm_val,
    pairing.partner_involutive]

private theorem Pairing.partnerSubtypePerm_ne_self {α : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (i : {i : α // p i}) :
    pairing.partnerSubtypePerm p hpartner i ≠ i := fun h =>
  pairing.partner_ne i (by rw [← pairing.partnerSubtypePerm_val p hpartner, h])

/-- Restricting a pairing partner to a partner-invariant subtype preserves the pairing property. -/
theorem Pairing.isPairing_partnerSubtypePerm {α : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i)) :
    IsPairing (pairing.partnerSubtypePerm p hpartner) :=
  ⟨pairing.partnerSubtypePerm_involutive p hpartner,
    pairing.partnerSubtypePerm_ne_self p hpartner⟩

/-- Restrict a pairing to a partner-invariant subtype and reindex the surviving positions by an
arbitrary equivalence with `Fin (2 * m)`. -/
noncomputable def Pairing.restrictAlongEquiv {α β : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (e : {i : α // p i} ≃ β) : PairingOn β :=
  Pairing.ofPartner
    (e.permCongr (pairing.partnerSubtypePerm p hpartner))
    (IsPairing.permCongr (pairing.isPairing_partnerSubtypePerm p hpartner) e)

/-- The restricted pairing partner agrees with the ambient partner through the chosen reindexing. -/
@[simp]
theorem Pairing.restrictAlongEquiv_partner {α β : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (e : {i : α // p i} ≃ β)
    (i : {i : α // p i}) :
    (pairing.restrictAlongEquiv p hpartner e).partner (e i) =
      e (pairing.partnerSubtypePerm p hpartner i) := by
  simp [Pairing.restrictAlongEquiv, Pairing.ofPartner, Equiv.permCongr_apply]

end Combinatorics
