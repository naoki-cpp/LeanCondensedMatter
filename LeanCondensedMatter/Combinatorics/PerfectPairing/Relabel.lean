import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Relabeling a `Pairing` along an ambient permutation

A pairing may be transported along an arbitrary permutation of its ambient ordered positions.
Crossing counts are not invariant under arbitrary relabeling and must be recomputed afterward.
-/

namespace Combinatorics

/-- Transport a pairing along an ambient relabeling `e`, where `e` maps new positions to old
positions. -/
def Pairing.relabel {n : ℕ} (P : Pairing n) (e : Equiv.Perm (Fin (2 * n))) : Pairing n where
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
theorem Pairing.relabel_partner {n : ℕ} (P : Pairing n) (e : Equiv.Perm (Fin (2 * n)))
    (i : Fin (2 * n)) : (P.relabel e).partner i = e.symm (P.partner (e i)) := by
  simp [Pairing.relabel]

/-- `Pairing.relabel` as an equivalence for a fixed ambient relabeling. -/
def Pairing.relabelEquiv {n : ℕ} (e : Equiv.Perm (Fin (2 * n))) : Pairing n ≃ Pairing n where
  toFun P := P.relabel e
  invFun P := P.relabel e.symm
  left_inv P := by
    ext i
    simp
  right_inv P := by
    ext i
    simp

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
