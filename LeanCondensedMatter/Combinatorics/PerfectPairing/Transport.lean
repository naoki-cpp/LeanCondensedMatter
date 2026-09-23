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

end Combinatorics
