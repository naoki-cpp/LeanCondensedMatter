import LeanCondensedMatter.Combinatorics.PerfectPairing.Core
import LeanCondensedMatter.Combinatorics.Common.DeletedFinPositions

set_option linter.style.header false

/-!
# Removing position `0` and its partner from a `Pairing (n + 1)`

`Pairing.eraseZeroPair` removes position `0` and its partner, reindexing the remaining positions
in increasing order via `Combinatorics/Common/DeletedFinPositions.lean`'s
`deletedPositionsOrderIso`. This is the combinatorial deletion step the finite-temperature
Bloch–de Dominicis induction recurses on; `Pairing.insertFirstPair`
(`PerfectPairing/InsertFirstPair.lean`) is its constructive counterpart.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- The underlying map of `restrictedPartner`, `x ↦ partner x`, landing back in the same deleted
positions: `partner` sends any position other than `0`/`partner 0` to another such position,
since `partner` is an involution and `partner 0`'s own partner is `0`. Extracted once and used for
both `restrictedPartner`'s `toFun` and `invFun` (an involution has a single underlying map, used
in both directions), rather than duplicating this argument. -/
def Pairing.restrictedPartnerMap {n : ℕ} (pairing : Pairing (n + 1))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ pairing.partner 0)
    (x : deletedPositions n (pairing.partner 0) hzero) :
    deletedPositions n (pairing.partner 0) hzero := by
  have hxj : (x : Fin (2 * (n + 1))) ≠ pairing.partner 0 :=
    (Finset.mem_erase.mp x.property).1
  have hx0 : (x : Fin (2 * (n + 1))) ≠ 0 :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp x.property).2).1
  have hpxj : pairing.partner x ≠ pairing.partner 0 := by
    intro h
    apply hx0
    calc
      (x : Fin (2 * (n + 1))) = pairing.partner (pairing.partner x) :=
        (pairing.partner_partner x).symm
      _ = pairing.partner (pairing.partner 0) := by rw [h]
      _ = 0 := pairing.partner_partner 0
  have hpx0 : pairing.partner x ≠ 0 := by
    intro h
    apply hxj
    calc
      (x : Fin (2 * (n + 1))) = pairing.partner (pairing.partner x) :=
        (pairing.partner_partner x).symm
      _ = pairing.partner 0 := by rw [h]
  exact ⟨pairing.partner x,
    Finset.mem_erase.mpr ⟨hpxj, Finset.mem_erase.mpr ⟨hpx0, Finset.mem_univ _⟩⟩⟩

/-- Restrict a pairing partner permutation to the positions left after removing `0` and its
partner.  The order-isomorphism back to `Fin (2 * n)` is applied by `eraseZeroPair`. -/
def Pairing.restrictedPartner {n : ℕ} (pairing : Pairing (n + 1))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ pairing.partner 0) :
    deletedPositions n (pairing.partner 0) hzero ≃
      deletedPositions n (pairing.partner 0) hzero where
  toFun := pairing.restrictedPartnerMap hzero
  invFun := pairing.restrictedPartnerMap hzero
  left_inv x := by
    apply Subtype.ext
    exact pairing.partner_partner x
  right_inv x := by
    apply Subtype.ext
    exact pairing.partner_partner x

@[simp]
theorem Pairing.restrictedPartner_partner_partner {n : ℕ} (pairing : Pairing (n + 1))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ pairing.partner 0)
    (x : deletedPositions n (pairing.partner 0) hzero) :
    pairing.restrictedPartner hzero (pairing.restrictedPartner hzero x) = x := by
  apply Subtype.ext
  exact pairing.partner_partner x

/-- Remove position `0` and its partner, reindexing the remaining positions in increasing order.

The resulting pairing is the combinatorial deletion step used by the finite-temperature
Bloch--de Dominicis induction. -/
noncomputable def Pairing.eraseZeroPair {n : ℕ} (pairing : Pairing (n + 1)) : Pairing n := by
  let hzero : (0 : Fin (2 * (n + 1))) ≠ pairing.partner 0 :=
    Ne.symm (pairing.partner_ne 0)
  let e := deletedPositionsOrderIso n (pairing.partner 0) hzero
  let r := pairing.restrictedPartner hzero
  let newPartner : Equiv.Perm (Fin (2 * n)) :=
    e.toEquiv.trans (r.trans e.symm.toEquiv)
  refine
    { partner := newPartner
      partner_involutive := ?_
      partner_ne_self := ?_ }
  · intro i
    dsimp [newPartner]
    rw [e.apply_symm_apply]
    rw [Pairing.restrictedPartner_partner_partner]
    exact e.symm_apply_apply i
  · intro i hi
    have hfixed : r (e i) = e i := by
      have h := congrArg e hi
      simpa [newPartner] using h
    have hpartner : pairing.partner (e i) = (e i : Fin (2 * (n + 1))) := by
      exact congrArg Subtype.val hfixed
    exact pairing.partner_ne (e i) hpartner

theorem Pairing.eraseZeroPair_partner_apply {n : ℕ} (pairing : Pairing (n + 1))
    (i : Fin (2 * n)) :
    (pairing.eraseZeroPair).partner i =
      let hzero : (0 : Fin (2 * (n + 1))) ≠ pairing.partner 0 :=
        Ne.symm (pairing.partner_ne 0)
      let e := deletedPositionsOrderIso n (pairing.partner 0) hzero
      e.symm (pairing.restrictedPartner hzero (e i)) := by
  simp [Pairing.eraseZeroPair]

/-- The order isomorphism used by `eraseZeroPair`, exposed as a named interface for later
induction lemmas. -/
noncomputable def Pairing.eraseZeroOrderIso {n : ℕ} (pairing : Pairing (n + 1)) :
    Fin (2 * n) ≃o
      deletedPositions n (pairing.partner 0)
        (Ne.symm (pairing.partner_ne 0)) :=
  deletedPositionsOrderIso n (pairing.partner 0) (Ne.symm (pairing.partner_ne 0))

@[simp]
theorem Pairing.eraseZeroOrderIso_partner {n : ℕ} (pairing : Pairing (n + 1))
    (i : Fin (2 * n)) :
    ((pairing.eraseZeroOrderIso ((pairing.eraseZeroPair).partner i) :
      Fin (2 * (n + 1)))) =
    pairing.partner (pairing.eraseZeroOrderIso i) := by
  simp [Pairing.eraseZeroOrderIso, Pairing.eraseZeroPair_partner_apply]
  rfl

theorem Pairing.eraseZeroPair_mem_pairs_iff {n : ℕ} (pairing : Pairing (n + 1))
    (i k : Fin (2 * n)) :
    (i, k) ∈ (pairing.eraseZeroPair).pairs ↔
      ((pairing.eraseZeroOrderIso i : Fin (2 * (n + 1))),
        (pairing.eraseZeroOrderIso k : Fin (2 * (n + 1)))) ∈ pairing.pairs := by
  rw [Pairing.mem_pairs_iff, Pairing.mem_pairs_iff]
  constructor
  · rintro ⟨hik, hpartner⟩
    refine ⟨pairing.eraseZeroOrderIso.strictMono hik, ?_⟩
    have hp := Pairing.eraseZeroOrderIso_partner pairing i
    rw [hpartner] at hp
    exact hp.symm
  · rintro ⟨hik, hpartner⟩
    have hik' : i < k := by
      have h := pairing.eraseZeroOrderIso.symm.strictMono hik
      simpa using h
    refine ⟨hik', ?_⟩
    apply pairing.eraseZeroOrderIso.injective
    apply Subtype.ext
    calc
      pairing.eraseZeroOrderIso ((pairing.eraseZeroPair).partner i) =
          pairing.partner (pairing.eraseZeroOrderIso i) :=
        Pairing.eraseZeroOrderIso_partner pairing i
      _ = pairing.eraseZeroOrderIso k := hpartner

end BlochDeDominicis
end Common
end SecondQuantization
