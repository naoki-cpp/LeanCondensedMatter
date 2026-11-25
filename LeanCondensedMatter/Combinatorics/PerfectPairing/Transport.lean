import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Transporting pairings

A `PairingOn` may be transported along an arbitrary equivalence between ambient types. The ordered
finite `Pairing n` inherits this operation directly; ordering-dependent quantities such as crossing
counts must be recomputed after arbitrary transport.
-/

namespace Combinatorics

/-- Transport a pairing along an ambient equivalence `e`, where `e` maps new positions to old
positions. -/
def PairingOn.transport {α β : Type*} (P : PairingOn β) (e : α ≃ β) : PairingOn α :=
  PairingOn.ofPartner (e.symm.permCongr P.partner) (by
    constructor
    · intro x
      simp [Equiv.permCongr_apply, P.partner_involutive (e x)]
    · intro x hx
      rw [Equiv.permCongr_apply] at hx
      apply P.partner_ne (e x)
      apply e.symm.injective
      simpa using hx)

@[simp]
theorem PairingOn.transport_partner {α β : Type*} (P : PairingOn β)
    (e : α ≃ β) (i : α) :
    (P.transport e).partner i = e.symm (P.partner (e i)) := by
  change (e.symm.permCongr P.partner) i = _
  rw [Equiv.permCongr_apply]
  rfl

/-- Casting a pair count is transport along the induced equality of flattened positions. -/
theorem Pairing.cast_eq_transport {m n : ℕ} (h : m = n) (P : Pairing m) :
    Equiv.cast (congrArg Pairing h) P =
      P.transport (finCongr (congrArg (fun k : ℕ => 2 * k) h)).symm := by
  subst n
  apply PairingOn.ext
  apply Equiv.ext
  intro p
  rw [PairingOn.transport_partner]
  rfl

/-- Casting the number of pairs transports the partner permutation through the corresponding
cast of flattened positions. -/
theorem Pairing.cast_partner {m n : ℕ} (h : m = n)
    (pairing : Pairing m) (p : Fin (2 * n)) :
    (finCongr (congrArg (fun k : ℕ => 2 * k) h.symm))
        ((Equiv.cast (congrArg Pairing h) pairing).partner p) =
      pairing.partner
        ((finCongr (congrArg (fun k : ℕ => 2 * k) h.symm)) p) := by
  subst n
  rfl

@[simp]
theorem PairingOn.transport_symm_transport {α β : Type*} (P : PairingOn β)
    (e : α ≃ β) :
    (P.transport e).transport e.symm = P := by
  ext i
  simp

@[simp]
theorem PairingOn.transport_transport_symm {α β : Type*} (P : PairingOn α)
    (e : α ≃ β) :
    (P.transport e.symm).transport e = P := by
  ext i
  simp

theorem PairingOn.transport_trans {α β γ : Type*} (P : PairingOn γ)
    (e : β ≃ γ) (f : α ≃ β) :
    (P.transport e).transport f = P.transport (f.trans e) := by
  ext i
  simp

/-- Conjugating each local perfect pairing by its own slot equivalence
commutes with assembling the complete independent block pairing. -/
theorem PairingOn.sigmaCongrRight_transport
    {ι : Type*} {β γ : ι → Type*}
    (P : ∀ i, PairingOn (β i))
    (e : ∀ i, β i ≃ γ i) :
    PairingOn.sigmaCongrRight
        (fun i => (P i).transport (e i).symm) =
      (PairingOn.sigmaCongrRight P).transport
        (Equiv.sigmaCongrRight e).symm := by
  apply PairingOn.ext
  apply Equiv.ext
  rintro ⟨i, x⟩
  have hsymm :
      (Equiv.sigmaCongrRight e).symm ⟨i, x⟩ =
        ⟨i, (e i).symm x⟩ := by
    apply (Equiv.sigmaCongrRight e).injective
    simp only [Equiv.apply_symm_apply, Equiv.sigmaCongrRight_apply]
  simp [PairingOn.transport_partner,
    PairingOn.sigmaCongrRight_partner, hsymm]

end Combinatorics
