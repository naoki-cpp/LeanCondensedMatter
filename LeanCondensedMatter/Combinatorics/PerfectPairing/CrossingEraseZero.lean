import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing
import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZero

set_option linter.style.header false

/-!
# `crossingCount` splits along `firstPair`/`eraseZeroPair`

`Pairing.crossingCount_eraseZeroPair` splits a pairing's total crossing count into crossings
entirely among the remaining pairs after removing `firstPair` (`eraseZeroPair.crossingCount`) plus
crossings with `firstPair` itself (`crossingsWithFirstPair`).
`Pairing.crossingsWithFirstPair_mod_two` further identifies `crossingsWithFirstPair`'s parity with
`interveningPositionCount`'s (the number of positions strictly between `0` and its partner) — the
exponent-recurrence fact `Common/BlochDeDominicis/PairingWeight.lean`'s `weight_eraseZeroPair`
builds the induction's sign-matching step on.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

theorem Pairing.eraseZeroPair_crosses_iff {n : ℕ} (pairing : Pairing (n + 1))
    (i k p q : Fin (2 * n)) :
    Crosses (i, k) (p, q) ↔
      Crosses
        ((pairing.eraseZeroOrderIso i : Fin (2 * (n + 1))),
          (pairing.eraseZeroOrderIso k : Fin (2 * (n + 1))))
        ((pairing.eraseZeroOrderIso p : Fin (2 * (n + 1))),
          (pairing.eraseZeroOrderIso q : Fin (2 * (n + 1)))) := by
  constructor
  · rintro ⟨hik, hkp, hpq⟩
    exact ⟨pairing.eraseZeroOrderIso.strictMono hik,
      pairing.eraseZeroOrderIso.strictMono hkp,
      pairing.eraseZeroOrderIso.strictMono hpq⟩
  · rintro ⟨hik, hkp, hpq⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using pairing.eraseZeroOrderIso.symm.strictMono hik
    · simpa using pairing.eraseZeroOrderIso.symm.strictMono hkp
    · simpa using pairing.eraseZeroOrderIso.symm.strictMono hpq

/-- Every normalized pair other than `firstPair` has both endpoints away from `0` and its
partner: this is what lets `eraseZeroOrderIso.symm` be applied to it. -/
theorem Pairing.mem_pairs_endpoints_mem_deletedPositions {n : ℕ} (pairing : Pairing (n + 1))
    {p : Fin (2 * (n + 1)) × Fin (2 * (n + 1))} (hp : p ∈ pairing.pairs)
    (hne : p ≠ pairing.firstPair) :
    p.1 ∈ deletedPositions n (pairing.partner 0) (Ne.symm (pairing.partner_ne 0)) ∧
      p.2 ∈ deletedPositions n (pairing.partner 0) (Ne.symm (pairing.partner_ne 0)) := by
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

/-- The crossing count splits along the pair containing position `0`: crossings entirely among
the remaining pairs (`eraseZeroPair.crossingCount`) plus crossings with `firstPair`
(`crossingsWithFirstPair`). -/
theorem Pairing.crossingCount_eraseZeroPair {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.crossingCount =
      pairing.eraseZeroPair.crossingCount + pairing.crossingsWithFirstPair := by
  classical
  set F := pairing.firstPair with hF
  set S := pairing.pairs with hS
  set A := S.erase F with hA
  have hFmem : F ∈ S := pairing.firstPair_mem_pairs
  have hFnotA : F ∉ A := fun h => (Finset.mem_erase.mp h).1 rfl
  have hsplit : S = insert F A := (Finset.insert_erase hFmem).symm
  have hsum : pairing.crossingCount =
      (S.filter (fun q => Crosses F q)).card + ∑ p ∈ A, (S.filter (fun q => Crosses p q)).card := by
    rw [Pairing.crossingCount, ← hS, card_filter_crosses_product_eq_sum, hsplit,
      Finset.sum_insert hFnotA, ← hsplit]
  have hFterm : (S.filter (fun q => Crosses F q)).card = pairing.crossingsWithFirstPair := rfl
  have hAterm : ∀ p ∈ A, S.filter (fun q => Crosses p q) = A.filter (fun q => Crosses p q) := by
    intro p _
    rw [hsplit, Finset.filter_insert, if_neg (not_crosses_firstPair pairing p)]
  have hsum' : pairing.crossingCount =
      pairing.crossingsWithFirstPair + ∑ p ∈ A, (A.filter (fun q => Crosses p q)).card := by
    rw [hsum, hFterm]
    congr 1
    exact Finset.sum_congr rfl fun p hp => by rw [hAterm p hp]
  have hAcross : ((A.product A).filter (fun pp => Crosses pp.1 pp.2)).card =
      ∑ p ∈ A, (A.filter (fun q => Crosses p q)).card :=
    card_filter_crosses_product_eq_sum A
  have hbij :
      ((pairing.eraseZeroPair.pairs.product pairing.eraseZeroPair.pairs).filter
        (fun pp => Crosses pp.1 pp.2)).card =
      ((A.product A).filter (fun pp => Crosses pp.1 pp.2)).card := by
    classical
    let mapPair : Fin (2 * n) × Fin (2 * n) → Fin (2 * (n + 1)) × Fin (2 * (n + 1)) :=
      fun P => (pairing.eraseZeroOrderIso P.1, pairing.eraseZeroOrderIso P.2)
    have hmapPair_ne_zero : ∀ P : Fin (2 * n) × Fin (2 * n), (mapPair P).1 ≠ 0 := by
      intro P
      have := (pairing.eraseZeroOrderIso P.1).property
      simp only [deletedPositions, Finset.mem_erase] at this
      exact this.2.1
    apply Finset.card_bij
      (i := fun (PQ : (Fin (2 * n) × Fin (2 * n)) × (Fin (2 * n) × Fin (2 * n))) _ =>
        (mapPair PQ.1, mapPair PQ.2))
    · rintro ⟨P, Q⟩ hPQ
      simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at hPQ ⊢
      obtain ⟨⟨hP, hQ⟩, hcross⟩ := hPQ
      have hPmem : mapPair P ∈ S := by
        rw [hS]
        exact (pairing.eraseZeroPair_mem_pairs_iff P.1 P.2).1 (by simpa using hP)
      have hQmem : mapPair Q ∈ S := by
        rw [hS]
        exact (pairing.eraseZeroPair_mem_pairs_iff Q.1 Q.2).1 (by simpa using hQ)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hA]
        exact Finset.mem_erase.2 ⟨fun h => hmapPair_ne_zero P (by rw [h]; rfl), hPmem⟩
      · rw [hA]
        exact Finset.mem_erase.2 ⟨fun h => hmapPair_ne_zero Q (by rw [h]; rfl), hQmem⟩
      · exact (pairing.eraseZeroPair_crosses_iff P.1 P.2 Q.1 Q.2).1 (by simpa using hcross)
    · rintro ⟨P, Q⟩ _ ⟨P', Q'⟩ _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hPeq : P = P' := by
        apply Prod.ext
        · exact pairing.eraseZeroOrderIso.injective (Subtype.ext (congrArg Prod.fst h1))
        · exact pairing.eraseZeroOrderIso.injective (Subtype.ext (congrArg Prod.snd h1))
      have hQeq : Q = Q' := by
        apply Prod.ext
        · exact pairing.eraseZeroOrderIso.injective (Subtype.ext (congrArg Prod.fst h2))
        · exact pairing.eraseZeroOrderIso.injective (Subtype.ext (congrArg Prod.snd h2))
      rw [hPeq, hQeq]
    · rintro ⟨p, q⟩ hpq
      simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at hpq
      obtain ⟨⟨hp, hq⟩, hcross⟩ := hpq
      have hpS : p ∈ S := (Finset.mem_erase.mp (hA ▸ hp)).2
      have hqS : q ∈ S := (Finset.mem_erase.mp (hA ▸ hq)).2
      have hpF : p ≠ F := (Finset.mem_erase.mp (hA ▸ hp)).1
      have hqF : q ≠ F := (Finset.mem_erase.mp (hA ▸ hq)).1
      obtain ⟨hp1, hp2⟩ := pairing.mem_pairs_endpoints_mem_deletedPositions hpS hpF
      obtain ⟨hq1, hq2⟩ := pairing.mem_pairs_endpoints_mem_deletedPositions hqS hqF
      refine ⟨(⟨(pairing.eraseZeroOrderIso.symm ⟨p.1, hp1⟩ : Fin (2 * n)),
          (pairing.eraseZeroOrderIso.symm ⟨p.2, hp2⟩ : Fin (2 * n))⟩,
        ⟨(pairing.eraseZeroOrderIso.symm ⟨q.1, hq1⟩ : Fin (2 * n)),
          (pairing.eraseZeroOrderIso.symm ⟨q.2, hq2⟩ : Fin (2 * n))⟩), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [pairing.eraseZeroPair_mem_pairs_iff]
          simp only [OrderIso.apply_symm_apply]
          rwa [Prod.mk.eta]
        · rw [pairing.eraseZeroPair_mem_pairs_iff]
          simp only [OrderIso.apply_symm_apply]
          rwa [Prod.mk.eta]
        · rw [pairing.eraseZeroPair_crosses_iff]
          simp only [OrderIso.apply_symm_apply]
          rwa [Prod.mk.eta, Prod.mk.eta]
      · simp only [mapPair, OrderIso.apply_symm_apply, Prod.mk.eta]
  rw [hsum', ← hAcross, Pairing.crossingCount, hbij]
  omega

/-- The number of positions strictly between `0` and its partner. -/
def Pairing.interveningPositionCount {n : ℕ} (pairing : Pairing (n + 1)) : ℕ :=
  (pairing.partner 0).val - 1

/-- `firstPair`'s crossings correspond exactly to intervening positions whose partner lies past
`partner 0`; the remaining intervening positions pair off amongst themselves and so contribute an
even count. Hence `crossingsWithFirstPair` and `interveningPositionCount` agree mod `2`. -/
theorem Pairing.crossingsWithFirstPair_mod_two {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.crossingsWithFirstPair % 2 = pairing.interveningPositionCount % 2 := by
  classical
  set j : Fin (2 * (n + 1)) := pairing.partner 0 with hj
  set I : Finset (Fin (2 * (n + 1))) := Finset.Ioo 0 j with hI
  set C : Finset (Fin (2 * (n + 1))) := I.filter (fun k => j < pairing.partner k) with hC
  set D : Finset (Fin (2 * (n + 1))) := I.filter (fun k => pairing.partner k < j) with hD
  have hpartner_ne0 : ∀ k ∈ I, pairing.partner k ≠ 0 := by
    intro k hk h
    have hkj : k = j := by
      have h' := congrArg pairing.partner h
      rwa [pairing.partner_partner, ← hj] at h'
    have hklt : k < j := (Finset.mem_Ioo.mp hk).2
    rw [hkj] at hklt
    exact lt_irrefl _ hklt
  have hpartner_nej : ∀ k ∈ I, pairing.partner k ≠ j := by
    intro k hk h
    have hk0 : (0 : Fin (2 * (n + 1))) < k := (Finset.mem_Ioo.mp hk).1
    have hk0' : k = 0 := by
      have heq : pairing.partner k = pairing.partner 0 := by rw [h, hj]
      exact pairing.partner.injective heq
    rw [hk0'] at hk0
    exact lt_irrefl _ hk0
  have hsplitI : I = D ∪ C := by
    ext k
    simp only [hD, hC, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hk
      rcases lt_trichotomy (pairing.partner k) j with h | h | h
      · exact Or.inl ⟨hk, h⟩
      · exact absurd h (hpartner_nej k hk)
      · exact Or.inr ⟨hk, h⟩
    · rintro (⟨hk, -⟩ | ⟨hk, -⟩) <;> exact hk
  have hdisjDC : Disjoint D C := by
    rw [Finset.disjoint_left]
    intro k hkD hkC
    exact absurd (Finset.mem_filter.mp hkD).2 (not_lt.mpr (Finset.mem_filter.mp hkC).2.le)
  have hCcard : C.card = pairing.crossingsWithFirstPair := by
    rw [Pairing.crossingsWithFirstPair]
    apply Finset.card_bij' (fun k _ => (k, pairing.partner k)) (fun pq _ => pq.1)
    · intro k hk
      simp only [hC, Finset.mem_filter, hI, Finset.mem_Ioo] at hk
      obtain ⟨⟨hk0, hkj⟩, hkgt⟩ := hk
      simp only [Finset.mem_filter]
      refine ⟨(pairing.mem_pairs_iff k (pairing.partner k)).2 ⟨?_, rfl⟩, ?_, ?_, ?_⟩
      · exact hkj.trans hkgt
      · exact hk0
      · exact hkj
      · exact hkgt
    · intro pq hpq
      simp only [Finset.mem_filter] at hpq
      obtain ⟨hpqmem, h1, h2, h3⟩ := hpq
      simp only [hC, Finset.mem_filter, hI, Finset.mem_Ioo]
      have hpartner : pairing.partner pq.1 = pq.2 := ((pairing.mem_pairs_iff pq.1 pq.2).1 hpqmem).2
      exact ⟨⟨h1, h2⟩, by rw [hpartner]; exact h3⟩
    · intro k _
      rfl
    · intro pq hpq
      simp only [Finset.mem_filter] at hpq
      obtain ⟨hpqmem, -, -, -⟩ := hpq
      have hpartner : pairing.partner pq.1 = pq.2 := ((pairing.mem_pairs_iff pq.1 pq.2).1 hpqmem).2
      exact Prod.ext rfl hpartner
  set A : Finset (Fin (2 * (n + 1))) := D.filter (fun k => k < pairing.partner k) with hA
  set B : Finset (Fin (2 * (n + 1))) := D.filter (fun k => pairing.partner k < k) with hB
  have hsplitD : D = A ∪ B := by
    ext k
    simp only [hA, hB, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hk
      rcases lt_trichotomy k (pairing.partner k) with h | h | h
      · exact Or.inl ⟨hk, h⟩
      · exact absurd h.symm (pairing.partner_ne k)
      · exact Or.inr ⟨hk, h⟩
    · rintro (⟨hk, -⟩ | ⟨hk, -⟩) <;> exact hk
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro k hkA hkB
    exact absurd (Finset.mem_filter.mp hkA).2 (not_lt.mpr (Finset.mem_filter.mp hkB).2.le)
  have hAB : A.card = B.card := by
    apply Finset.card_bij' (fun k _ => pairing.partner k) (fun k _ => pairing.partner k)
    · intro k hk
      simp only [hA, Finset.mem_filter] at hk
      obtain ⟨hkD, hklt⟩ := hk
      simp only [hB, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · simp only [hD, hI, Finset.mem_filter, Finset.mem_Ioo] at hkD ⊢
        obtain ⟨⟨h1, h2⟩, h3⟩ := hkD
        exact ⟨⟨h1.trans hklt, h3⟩, by rw [pairing.partner_partner]; exact h2⟩
      · rw [pairing.partner_partner]; exact hklt
    · intro k hk
      simp only [hB, Finset.mem_filter] at hk
      obtain ⟨hkD, hklt⟩ := hk
      simp only [hA, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · simp only [hD, hI, Finset.mem_filter, Finset.mem_Ioo] at hkD ⊢
        obtain ⟨⟨h1, h2⟩, h3⟩ := hkD
        have hpos : (0 : Fin (2 * (n + 1))) < pairing.partner k :=
          lt_of_le_of_ne (Fin.zero_le _)
            (Ne.symm (hpartner_ne0 k (Finset.mem_Ioo.mpr ⟨h1, h2⟩)))
        exact ⟨⟨hpos, h3⟩, by rw [pairing.partner_partner]; exact h2⟩
      · rw [pairing.partner_partner]; exact hklt
    · intro k _
      exact pairing.partner_partner k
    · intro k _
      exact pairing.partner_partner k
  have hDcard : D.card = 2 * A.card := by
    rw [hsplitD, Finset.card_union_of_disjoint hdisjAB, hAB]
    ring
  have hIcard : I.card = D.card + C.card := by
    rw [hsplitI, Finset.card_union_of_disjoint hdisjDC]
  have hIcard' : I.card = pairing.interveningPositionCount := by
    rw [hI, Fin.card_Ioo, Pairing.interveningPositionCount, hj]
    simp
  have hfinal : pairing.interveningPositionCount = 2 * A.card + pairing.crossingsWithFirstPair := by
    rw [← hIcard', hIcard, hDcard, hCcard]
  omega

end BlochDeDominicis
end Common
end SecondQuantization
