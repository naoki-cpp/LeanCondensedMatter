import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Relabeling a `Pairing` along an ambient permutation

Step 6 (PR 5b) of the diagram-connectedness plan (`notes/roadmaps/second-quantization.md`):
transporting a `Pairing n` along an arbitrary `Equiv.Perm (Fin (2 * n))` relabeling of its
positions. Needed to move `QuarticWickDiagram.pairing` (stored on the diagram's own fixed leg
enumeration, `quarticLegEquiv`) onto the leg enumeration induced by an arbitrary vertex order
`Fin S.card ≃ ↥S`.

**No claim that the crossing weight `Pairing.weight` is relabel-invariant** — it is not, for an
arbitrary permutation `e` (crossing count depends on the ambient linear order on `Fin (2 * n)`,
which an arbitrary relabeling does not preserve). Callers must recompute `weight` on the relabeled
pairing itself, not reuse the original pairing's weight.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- **Transport a pairing along an ambient relabeling** `e`, understood as mapping *new* positions
to the *old* positions on which `P` is stored: position `i`'s partner in the relabeled pairing is
found by looking up `P`'s partner of `e i` (an old position), then translating that partner back
to a new position via `e.symm`. -/
def Pairing.relabel {n : ℕ} (P : Pairing n) (e : Equiv.Perm (Fin (2 * n))) : Pairing n where
  partner := e.trans (P.partner.trans e.symm)
  partner_involutive := by
    intro i
    simp
  partner_ne_self := by
    intro i h
    apply P.partner_ne (e i)
    have := congrArg e h
    simpa using this

@[simp]
theorem Pairing.relabel_partner {n : ℕ} (P : Pairing n) (e : Equiv.Perm (Fin (2 * n)))
    (i : Fin (2 * n)) : (P.relabel e).partner i = e.symm (P.partner (e i)) := by
  simp [Pairing.relabel]

/-- **`Pairing.relabel` as an equivalence** `Pairing n ≃ Pairing n`, for a fixed ambient
relabeling `e`. -/
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

end BlochDeDominicis
end Common
end SecondQuantization
