import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Transporting and relabeling pairings

A `PairingOn` may be transported along an arbitrary equivalence between ambient types. Relabeling is
the same construction specialized to a permutation of one type. The ordered finite `Pairing n`
inherits these operations directly; crossing counts remain order-dependent and must be recomputed
after arbitrary relabeling.
-/

namespace Combinatorics

/-- Transport a pairing along an ambient equivalence `e`, where `e` maps new positions to old
positions. -/
def PairingOn.transport {α β : Type*} (P : PairingOn β) (e : α ≃ β) : PairingOn α :=
  PairingOn.ofPartner (e.symm.permCongr P.partner)
    (IsPairing.permCongr P.isPairing e.symm)

@[simp]
theorem PairingOn.transport_partner {α β : Type*} (P : PairingOn β)
    (e : α ≃ β) (i : α) :
    (P.transport e).partner i = e.symm (P.partner (e i)) := by
  simp [PairingOn.transport, Equiv.permCongr_apply]

/-- `PairingOn.transport` as an equivalence for a fixed ambient equivalence. -/
def PairingOn.transportEquiv {α β : Type*} (e : α ≃ β) :
    PairingOn β ≃ PairingOn α where
  toFun P := P.transport e
  invFun P := P.transport e.symm
  left_inv P := by
    ext i
    simp
  right_inv P := by
    ext i
    simp

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

/-- Transport a pairing along an ambient permutation, where `e` maps new positions to old
positions. -/
def PairingOn.relabel {α : Type*} (P : PairingOn α) (e : Equiv.Perm α) : PairingOn α :=
  P.transport e

@[simp]
theorem PairingOn.relabel_partner {α : Type*} (P : PairingOn α) (e : Equiv.Perm α)
    (i : α) : (P.relabel e).partner i = e.symm (P.partner (e i)) := by
  simp [PairingOn.relabel]

/-- `PairingOn.relabel` as an equivalence for a fixed ambient relabeling. -/
def PairingOn.relabelEquiv {α : Type*} (e : Equiv.Perm α) : PairingOn α ≃ PairingOn α :=
  PairingOn.transportEquiv e

@[simp]
theorem PairingOn.relabel_refl {α : Type*} (P : PairingOn α) :
    P.relabel (Equiv.refl α) = P := by
  ext i
  simp

@[simp]
theorem PairingOn.relabel_symm_relabel {α : Type*} (P : PairingOn α) (e : Equiv.Perm α) :
    (P.relabel e).relabel e.symm = P := by
  ext i
  simp

@[simp]
theorem PairingOn.relabel_relabel_symm {α : Type*} (P : PairingOn α) (e : Equiv.Perm α) :
    (P.relabel e.symm).relabel e = P := by
  ext i
  simp

theorem PairingOn.relabel_trans {α : Type*} (P : PairingOn α) (e f : Equiv.Perm α) :
    (P.relabel e).relabel f = P.relabel (f.trans e) := by
  ext i
  simp

end Combinatorics
