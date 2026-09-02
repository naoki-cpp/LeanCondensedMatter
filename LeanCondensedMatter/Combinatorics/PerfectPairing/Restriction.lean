import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Restricting a perfect pairing to an invariant subset

A pairing partner permutation can be restricted to any partner-invariant predicate on its ordered
positions. After choosing an equivalence from that invariant subtype to `Fin (2 * m)`, the
restricted fixed-point-free involution gives a `Pairing m`.

This module owns only the generic pairing construction. Diagrammatic users remain responsible for
proving that their selected legs are partner-invariant and for supplying the diagram-specific
reindexing equivalence.
-/

namespace Combinatorics

/-- Restrict the partner permutation of a pairing to a partner-invariant subtype. -/
noncomputable def Pairing.partnerSubtypePerm {n : ℕ} (pairing : Pairing n)
    (p : Fin (2 * n) → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i)) :
    Equiv.Perm {i : Fin (2 * n) // p i} :=
  pairing.partner.subtypePerm fun i => (hpartner i).symm

@[simp]
theorem Pairing.partnerSubtypePerm_val {n : ℕ} (pairing : Pairing n)
    (p : Fin (2 * n) → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (i : {i : Fin (2 * n) // p i}) :
    ((pairing.partnerSubtypePerm p hpartner i : {i : Fin (2 * n) // p i}) : Fin (2 * n)) =
      pairing.partner i :=
  congrArg Subtype.val (Equiv.Perm.subtypePerm_apply _ _ i)

private theorem Pairing.partnerSubtypePerm_involutive {n : ℕ} (pairing : Pairing n)
    (p : Fin (2 * n) → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i)) :
    Function.Involutive (pairing.partnerSubtypePerm p hpartner) := fun i => by
  apply Subtype.ext
  rw [pairing.partnerSubtypePerm_val, pairing.partnerSubtypePerm_val,
    pairing.partner_involutive]

private theorem Pairing.partnerSubtypePerm_ne_self {n : ℕ} (pairing : Pairing n)
    (p : Fin (2 * n) → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (i : {i : Fin (2 * n) // p i}) :
    pairing.partnerSubtypePerm p hpartner i ≠ i := fun h =>
  pairing.partner_ne i (by rw [← pairing.partnerSubtypePerm_val p hpartner, h])

/-- Restricting a pairing partner to a partner-invariant subtype preserves the pairing property. -/
theorem Pairing.isPairing_partnerSubtypePerm {n : ℕ} (pairing : Pairing n)
    (p : Fin (2 * n) → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i)) :
    IsPairing (pairing.partnerSubtypePerm p hpartner) :=
  ⟨pairing.partnerSubtypePerm_involutive p hpartner,
    pairing.partnerSubtypePerm_ne_self p hpartner⟩

/-- Restrict a pairing to a partner-invariant subtype and reindex the surviving positions by an
arbitrary equivalence with `Fin (2 * m)`. -/
noncomputable def Pairing.restrictAlongEquiv {n m : ℕ} (pairing : Pairing n)
    (p : Fin (2 * n) → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (e : {i : Fin (2 * n) // p i} ≃ Fin (2 * m)) : Pairing m :=
  Pairing.ofPartner
    (e.permCongr (pairing.partnerSubtypePerm p hpartner))
    (IsPairing.permCongr (pairing.isPairing_partnerSubtypePerm p hpartner) e)

/-- The restricted pairing partner agrees with the ambient partner through the chosen reindexing. -/
@[simp]
theorem Pairing.restrictAlongEquiv_partner {n m : ℕ} (pairing : Pairing n)
    (p : Fin (2 * n) → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (e : {i : Fin (2 * n) // p i} ≃ Fin (2 * m))
    (i : {i : Fin (2 * n) // p i}) :
    (pairing.restrictAlongEquiv p hpartner e).partner (e i) =
      e (pairing.partnerSubtypePerm p hpartner i) := by
  simp [Pairing.restrictAlongEquiv, Pairing.ofPartner, Equiv.permCongr_apply]

end Combinatorics
