import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction
import LeanCondensedMatter.Combinatorics.FiniteIndex.DeletedPositions

set_option linter.style.header false

/-!
# Removing position `0` and its partner from a `Pairing (n + 1)`

`Pairing.eraseZeroPair` removes position `0` and its partner, reindexing the remaining positions
through the pure finite-index API in `Combinatorics.FiniteIndex`.
-/

namespace Combinatorics

open FiniteIndex

/-- Remove position `0` and its partner, reindexing the remaining positions increasingly. -/
noncomputable def Pairing.eraseZeroPair {n : ℕ} (pairing : Pairing (n + 1)) : Pairing n := by
  let p := fun i : Fin (2 * (n + 1)) =>
    i ∈ deletedPositions n (pairing.partner 0)
  have hpartner : ∀ i, p i ↔ p (pairing.partner i) := by
    intro i
    simp only [p, deletedPositions, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨hpartner0, hzero⟩
      constructor
      · intro h
        exact hzero (pairing.partner.injective h)
      · intro h
        apply hpartner0
        calc
          i = pairing.partner (pairing.partner i) := (pairing.partner_partner i).symm
          _ = pairing.partner 0 := congrArg pairing.partner h
    · rintro ⟨hpartner0, hzero⟩
      constructor
      · intro h
        apply hzero
        calc
          pairing.partner i = pairing.partner (pairing.partner 0) :=
            congrArg pairing.partner h
          _ = 0 := pairing.partner_partner 0
      · intro h
        apply hpartner0
        simpa [h]
  let e :=
    deletedPositionsOrderIso n (pairing.partner 0) (pairing.partner_ne 0)
  exact pairing.restrictAlongEquiv p hpartner e.symm.toEquiv

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
  simp [Pairing.eraseZeroOrderIso, Pairing.eraseZeroPair, PairingOn.restrictAlongEquiv]

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
