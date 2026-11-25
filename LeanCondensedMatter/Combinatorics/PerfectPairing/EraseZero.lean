import LeanCondensedMatter.Combinatorics.PerfectPairing.Core
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
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
    i ∈ deletedPositions (2 * n) (pairing.partner 0)
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
    deletedPositionsOrderIso (2 * n) (pairing.partner 0) (pairing.partner_ne 0)
  exact pairing.restrictAlongEquiv p hpartner e.symm.toEquiv

/-- Increasing equivalence used by `eraseZeroPair`. -/
noncomputable def Pairing.eraseZeroOrderIso {n : ℕ} (pairing : Pairing (n + 1)) :
    Fin (2 * n) ≃o
      deletedPositions (2 * n) (pairing.partner 0) :=
  deletedPositionsOrderIso (2 * n) (pairing.partner 0) (pairing.partner_ne 0)

@[simp]
theorem Pairing.eraseZeroOrderIso_partner {n : ℕ} (pairing : Pairing (n + 1))
    (i : Fin (2 * n)) :
    ((pairing.eraseZeroOrderIso ((pairing.eraseZeroPair).partner i) :
      Fin (2 * (n + 1)))) =
    pairing.partner (pairing.eraseZeroOrderIso i) := by
  simp [Pairing.eraseZeroOrderIso, Pairing.eraseZeroPair, PairingOn.restrictAlongEquiv]

private theorem Pairing.eraseZeroPair_mem_pairs_iff {n : ℕ} (pairing : Pairing (n + 1))
    (i k : Fin (2 * n)) :
    (i, k) ∈ (pairing.eraseZeroPair).pairs ↔
      ((pairing.eraseZeroOrderIso i : Fin (2 * (n + 1))),
        (pairing.eraseZeroOrderIso k : Fin (2 * (n + 1)))) ∈ pairing.pairs := by
  let e : Fin (2 * n) ↪o Fin (2 * (n + 1)) :=
    OrderEmbedding.ofStrictMono (fun i => pairing.eraseZeroOrderIso i)
      (fun _ _ h => pairing.eraseZeroOrderIso.strictMono h)
  exact (pairing.eraseZeroPair.mem_pairs_map_iff pairing e
    (fun i => (pairing.eraseZeroOrderIso_partner i).symm) i k).symm

/-- Every normalized pair other than `firstPair` has both endpoints away from `0` and its
partner. -/
private theorem Pairing.mem_pairs_endpoints_mem_deletedPositions {n : ℕ} (pairing : Pairing (n + 1))
    {p : Fin (2 * (n + 1)) × Fin (2 * (n + 1))} (hp : p ∈ pairing.pairs)
    (hne : p ≠ pairing.firstPair) :
    p.1 ∈ deletedPositions (2 * n) (pairing.partner 0) ∧
      p.2 ∈ deletedPositions (2 * n) (pairing.partner 0) := by
  have hne' : (⟨p, hp⟩ : pairing.NormalizedPair) ≠
      ⟨pairing.firstPair, pairing.firstPair_mem_pairs⟩ :=
    fun h => hne (congrArg Subtype.val h)
  have h := pairing.normalizedPair_endpoints_ne_of_ne _ _ hne'
  change p.1 ≠ 0 ∧ p.1 ≠ pairing.partner 0 ∧
    p.2 ≠ 0 ∧ p.2 ≠ pairing.partner 0 at h
  obtain ⟨h10, h1j, h20, h2j⟩ := h
  simp [deletedPositions, h10, h1j, h20, h2j]

/-- Map a pair of remaining positions to its original ambient positions. -/
noncomputable def Pairing.eraseZeroPairEmbedding {n : ℕ} (pairing : Pairing (n + 1)) :
    (Fin (2 * n) × Fin (2 * n)) ↪
      (Fin (2 * (n + 1)) × Fin (2 * (n + 1))) where
  toFun pr := (pairing.eraseZeroOrderIso pr.1, pairing.eraseZeroOrderIso pr.2)
  inj' := by
    intro p q h
    exact Prod.ext
      (pairing.eraseZeroOrderIso.injective (Subtype.ext (congrArg Prod.fst h)))
      (pairing.eraseZeroOrderIso.injective (Subtype.ext (congrArg Prod.snd h)))

/-- The ambient pairs other than the first pair are exactly the embedded smaller pairing's pairs. -/
theorem Pairing.pairs_erase_firstPair_eq_image {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.pairs.erase pairing.firstPair =
      pairing.eraseZeroPair.pairs.image pairing.eraseZeroPairEmbedding := by
  classical
  ext p
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hne, hp⟩
    obtain ⟨h1, h2⟩ := pairing.mem_pairs_endpoints_mem_deletedPositions hp hne
    refine ⟨(pairing.eraseZeroOrderIso.symm ⟨p.1, h1⟩,
      pairing.eraseZeroOrderIso.symm ⟨p.2, h2⟩), ?_, ?_⟩
    · rw [pairing.eraseZeroPair_mem_pairs_iff]
      simpa using hp
    · change (↑(pairing.eraseZeroOrderIso (pairing.eraseZeroOrderIso.symm ⟨p.1, h1⟩)),
        ↑(pairing.eraseZeroOrderIso (pairing.eraseZeroOrderIso.symm ⟨p.2, h2⟩))) = p
      simp
  · rintro ⟨pr, hpr, rfl⟩
    refine ⟨?_, (pairing.eraseZeroPair_mem_pairs_iff pr.1 pr.2).1 hpr⟩
    intro heq
    have h0 : (pairing.eraseZeroOrderIso pr.1 : Fin (2 * (n + 1))) ≠ 0 :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp (pairing.eraseZeroOrderIso pr.1).property).2).1
    exact h0 (congrArg Prod.fst heq)

end Combinatorics
