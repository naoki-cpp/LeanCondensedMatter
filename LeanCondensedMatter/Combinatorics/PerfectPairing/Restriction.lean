import LeanCondensedMatter.Combinatorics.PerfectPairing.Transport

set_option linter.style.header false

/-!
# Restricting a pairing to an invariant subtype

A `PairingOn α` can be restricted to any partner-invariant predicate on `α`. The canonical
restriction is itself a `PairingOn` on the invariant subtype; an arbitrary equivalence may then
transport that pairing to any target type.

The ordered finite `Pairing n` inherits this construction directly. Diagrammatic users remain
responsible only for the invariant predicate and their domain-specific reindexing equivalence.
-/

namespace Combinatorics

/-- Restrict a pairing to a partner-invariant subtype. -/
noncomputable def PairingOn.restrict {α : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i)) :
    PairingOn {i : α // p i} where
  partner := pairing.partner.subtypePerm fun i => (hpartner i).symm
  partner_involutive := by
    intro i
    apply Subtype.ext
    simp only [Equiv.Perm.subtypePerm_apply]
    exact pairing.partner_involutive i
  partner_ne := by
    intro i hi
    apply pairing.partner_ne i
    have hv := congrArg Subtype.val hi
    simpa only [Equiv.Perm.subtypePerm_apply] using hv

/-- The restricted pairing has the ambient partner as its underlying value. -/
@[simp]
theorem PairingOn.restrict_partner_val {α : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (i : {i : α // p i}) :
    (((pairing.restrict p hpartner).partner i : {i : α // p i}) : α) =
      pairing.partner i :=
  congrArg Subtype.val
    (Equiv.Perm.subtypePerm_apply pairing.partner (fun x => (hpartner x).symm) i)

/-- Restrict a pairing to a partner-invariant subtype and transport the result along an arbitrary
equivalence to the target type. -/
noncomputable def PairingOn.restrictAlongEquiv {α β : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (e : {i : α // p i} ≃ β) : PairingOn β :=
  (pairing.restrict p hpartner).transport e.symm

/-- The transported restricted pairing agrees with the restricted partner under the chosen
equivalence. -/
@[simp]
theorem PairingOn.restrictAlongEquiv_partner {α β : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (e : {i : α // p i} ≃ β)
    (i : {i : α // p i}) :
    (pairing.restrictAlongEquiv p hpartner e).partner (e i) =
      e ((pairing.restrict p hpartner).partner i) := by
  simp [PairingOn.restrictAlongEquiv]


/-- Transporting a restricted partner back to the ambient subtype recovers the ambient partner
as its underlying value. -/
@[simp]
theorem PairingOn.restrictAlongEquiv_partner_symm_val {α β : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (e : {i : α // p i} ≃ β) (i : β) :
    ((e.symm ((pairing.restrictAlongEquiv p hpartner e).partner i) :
        {i : α // p i}) : α) =
      pairing.partner (e.symm i) := by
  let j := e.symm i
  have h := pairing.restrictAlongEquiv_partner p hpartner e j
  have h' := congrArg (fun q => ((e.symm q : {i : α // p i}) : α)) h
  simpa [j] using h'


end Combinatorics
