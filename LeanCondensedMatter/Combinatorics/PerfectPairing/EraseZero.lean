import LeanCondensedMatter.Combinatorics.PerfectPairing.Core
import LeanCondensedMatter.Combinatorics.FiniteIndex.DeletedPositions

set_option linter.style.header false

/-!
# Removing position `0` and its partner from a `Pairing (n + 1)`

`Pairing.eraseZeroPair` removes position `0` and its partner, reindexing the remaining positions
through the pure finite-index API in `Combinatorics.FiniteIndex`.
-/

namespace Combinatorics

open FiniteIndex

/-- The partner map restricted to the positions remaining after deleting `0` and `partner 0`. -/
def Pairing.restrictedPartnerMap {n : ℕ} (pairing : Pairing (n + 1))
    (x : deletedPositions n (pairing.partner 0)) :
    deletedPositions n (pairing.partner 0) := by
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

/-- Restrict a pairing partner permutation to the surviving positions. -/
def Pairing.restrictedPartner {n : ℕ} (pairing : Pairing (n + 1)) :
    deletedPositions n (pairing.partner 0) ≃
      deletedPositions n (pairing.partner 0) where
  toFun := pairing.restrictedPartnerMap
  invFun := pairing.restrictedPartnerMap
  left_inv x := Subtype.ext (pairing.partner_partner x)
  right_inv x := Subtype.ext (pairing.partner_partner x)

@[simp]
theorem Pairing.restrictedPartner_partner_partner {n : ℕ} (pairing : Pairing (n + 1))
    (x : deletedPositions n (pairing.partner 0)) :
    pairing.restrictedPartner (pairing.restrictedPartner x) = x :=
  Subtype.ext (pairing.partner_partner x)

/-- Remove position `0` and its partner, reindexing the remaining positions increasingly. -/
noncomputable def Pairing.eraseZeroPair {n : ℕ} (pairing : Pairing (n + 1)) : Pairing n := by
  let hzero : pairing.partner 0 ≠ (0 : Fin (2 * (n + 1))) := pairing.partner_ne 0
  let e := deletedPositionsOrderIso n (pairing.partner 0) hzero
  let r := pairing.restrictedPartner
  let newPartner : Equiv.Perm (Fin (2 * n)) :=
    e.toEquiv.trans (r.trans e.symm.toEquiv)
  refine
    { partner := newPartner
      partner_involutive := ?_
      partner_ne := ?_ }
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
      let hzero : pairing.partner 0 ≠ (0 : Fin (2 * (n + 1))) := pairing.partner_ne 0
      let e := deletedPositionsOrderIso n (pairing.partner 0) hzero
      e.symm (pairing.restrictedPartner (e i)) := by
  simp [Pairing.eraseZeroPair]

/-- Increasing equivalence used by `eraseZeroPair`. -/
noncomputable def Pairing.eraseZeroOrderIso {n : ℕ} (pairing : Pairing (n + 1)) :
    Fin (2 * n) ≃o
      deletedPositions n (pairing.partner 0) :=
  deletedPositionsOrderIso n (pairing.partner 0) (pairing.partner_ne 0)

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

end Combinatorics
