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

/-- Every normalized pair other than `firstPair` has both endpoints away from `0` and its
partner. -/
private theorem Pairing.mem_pairs_endpoints_mem_deletedPositions {n : ℕ} (pairing : Pairing (n + 1))
    {p : Fin (2 * (n + 1)) × Fin (2 * (n + 1))} (hp : p ∈ pairing.pairs)
    (hne : p ≠ pairing.firstPair) :
    p.1 ∈ deletedPositions n (pairing.partner 0) ∧
      p.2 ∈ deletedPositions n (pairing.partner 0) := by
  obtain ⟨hlt, hpartner⟩ := (pairing.mem_pairs_iff p.1 p.2).1 (by simpa using hp)
  have h10 : p.1 ≠ 0 := by
    intro h
    apply hne
    have h2 : p.2 = pairing.partner 0 := by rw [← hpartner, h]
    change p = pairing.firstPair
    rw [Pairing.firstPair]
    exact Prod.ext h h2
  have h1j : p.1 ≠ pairing.partner 0 := by
    intro h
    apply h10
    have hp2 : p.2 = 0 := by
      have := hpartner
      rw [h] at this
      rw [pairing.partner_partner] at this
      exact this.symm
    have : (pairing.partner 0 : Fin (2 * (n + 1))) < 0 := by rw [← h]; exact hp2 ▸ hlt
    exact absurd this (by simp)
  have h20 : p.2 ≠ 0 := fun h => absurd (h ▸ hlt) (by simp)
  have h2j : p.2 ≠ pairing.partner 0 := by
    intro h
    apply h10
    have hinj : Function.Injective pairing.partner := pairing.partner.injective
    apply hinj
    rw [hpartner, h]
  refine ⟨?_, ?_⟩
  · simp [deletedPositions, Finset.mem_erase, h10, h1j]
  · simp [deletedPositions, Finset.mem_erase, h20, h2j]

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
