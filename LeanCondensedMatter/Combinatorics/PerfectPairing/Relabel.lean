import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Transporting and relabeling a `Pairing`

A pairing may be transported along an arbitrary equivalence between its ambient ordered positions.
The equal-order specialization is the usual relabeling along a permutation. Crossing counts are not
invariant under arbitrary relabeling and must be recomputed afterward.
-/

namespace Combinatorics

/-- Transport a pairing along an ambient equivalence `e`, where `e` maps new positions to old
positions. -/
def Pairing.transport {m n : ℕ} (P : Pairing n) (e : Fin (2 * m) ≃ Fin (2 * n)) : Pairing m where
  partner := e.trans (P.partner.trans e.symm)
  partner_involutive := by
    intro i
    simp
  partner_ne := by
    intro i h
    apply P.partner_ne (e i)
    have := congrArg e h
    simpa using this

@[simp]
theorem Pairing.transport_partner {m n : ℕ} (P : Pairing n)
    (e : Fin (2 * m) ≃ Fin (2 * n)) (i : Fin (2 * m)) :
    (P.transport e).partner i = e.symm (P.partner (e i)) := by
  simp [Pairing.transport]

/-- `Pairing.transport` as an equivalence for a fixed ambient equivalence. -/
def Pairing.transportEquiv {m n : ℕ} (e : Fin (2 * m) ≃ Fin (2 * n)) :
    Pairing n ≃ Pairing m where
  toFun P := P.transport e
  invFun P := P.transport e.symm
  left_inv P := by
    ext i
    simp
  right_inv P := by
    ext i
    simp

/-- Transport a pairing along an ambient permutation, where `e` maps new positions to old
positions. -/
def Pairing.relabel {n : ℕ} (P : Pairing n) (e : Equiv.Perm (Fin (2 * n))) : Pairing n :=
  P.transport e

@[simp]
theorem Pairing.relabel_partner {n : ℕ} (P : Pairing n) (e : Equiv.Perm (Fin (2 * n)))
    (i : Fin (2 * n)) : (P.relabel e).partner i = e.symm (P.partner (e i)) := by
  simp [Pairing.relabel]

/-- `Pairing.relabel` as an equivalence for a fixed ambient relabeling. -/
def Pairing.relabelEquiv {n : ℕ} (e : Equiv.Perm (Fin (2 * n))) : Pairing n ≃ Pairing n :=
  Pairing.transportEquiv e

@[simp]
theorem Pairing.relabel_refl {n : ℕ} (P : Pairing n) :
    P.relabel (Equiv.refl (Fin (2 * n))) = P := by
  ext i
  simp

@[simp]
theorem Pairing.relabel_symm_relabel {n : ℕ} (P : Pairing n) (e : Equiv.Perm (Fin (2 * n))) :
    (P.relabel e).relabel e.symm = P := by
  ext i
  simp

@[simp]
theorem Pairing.relabel_relabel_symm {n : ℕ} (P : Pairing n) (e : Equiv.Perm (Fin (2 * n))) :
    (P.relabel e.symm).relabel e = P := by
  ext i
  simp

theorem Pairing.relabel_trans {n : ℕ} (P : Pairing n) (e f : Equiv.Perm (Fin (2 * n))) :
    (P.relabel e).relabel f = P.relabel (f.trans e) := by
  ext i
  simp

end Combinatorics
