import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing
import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZero
import LeanCondensedMatter.Combinatorics.Common.FinsetProduct

set_option linter.style.header false

/-!
# `crossingCount` splits along `firstPair`/`eraseZeroPair`

`Pairing.crossingCount_eraseZeroPair` splits a pairing's total crossing count into crossings
entirely among the remaining pairs after removing `firstPair` plus crossings with `firstPair`.
-/

namespace Combinatorics

open FiniteIndex

/-- The crossing count splits along the pair containing position `0`. -/
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
    rw [Pairing.crossingCount, ← hS, Finset.card_filter_product_eq_sum_card_filter, hsplit,
      Finset.sum_insert hFnotA, ← hsplit]
  have hFterm : (S.filter (fun q => Crosses F q)).card = pairing.crossingsWithFirstPair := rfl
  have hAterm : ∀ p ∈ A, S.filter (fun q => Crosses p q) = A.filter (fun q => Crosses p q) := by
    intro p _
    rw [hsplit, Finset.filter_insert, ite_eq_right (not_crosses_firstPair pairing p)]
  have hsum' : pairing.crossingCount =
      pairing.crossingsWithFirstPair + ∑ p ∈ A, (A.filter (fun q => Crosses p q)).card := by
    rw [hsum, hFterm]
    congr 1
    exact Finset.sum_congr rfl fun p hp => by rw [hAterm p hp]
  have hAcross : ((A.product A).filter (fun pp => Crosses pp.1 pp.2)).card =
      ∑ p ∈ A, (A.filter (fun q => Crosses p q)).card :=
    Finset.card_filter_product_eq_sum_card_filter A Crosses
  have hbij :
      ((pairing.eraseZeroPair.pairs.product pairing.eraseZeroPair.pairs).filter
        (fun pp => Crosses pp.1 pp.2)).card =
      ((A.product A).filter (fun pp => Crosses pp.1 pp.2)).card := by
    let mapPair := pairing.eraseZeroPairEmbedding
    have hAimage : A = pairing.eraseZeroPair.pairs.image mapPair :=
      pairing.pairs_erase_firstPair_eq_image
    apply Finset.card_bij
      (i := fun PQ _ => (mapPair PQ.1, mapPair PQ.2))
    · rintro ⟨P, Q⟩ hPQ
      simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at hPQ ⊢
      obtain ⟨⟨hP, hQ⟩, hcross⟩ := hPQ
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hAimage]
        exact Finset.mem_image.2 ⟨P, hP, rfl⟩
      · rw [hAimage]
        exact Finset.mem_image.2 ⟨Q, hQ, rfl⟩
      · exact (crosses_map_iff
          (fun i => (pairing.eraseZeroOrderIso i : Fin (2 * (n + 1))))
          pairing.eraseZeroOrderIso.strictMono P.1 P.2 Q.1 Q.2).2 hcross
    · rintro ⟨P, Q⟩ _ ⟨P', Q'⟩ _ h
      exact Prod.ext (mapPair.injective (congrArg Prod.fst h))
        (mapPair.injective (congrArg Prod.snd h))
    · rintro ⟨p, q⟩ hpq
      simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at hpq
      obtain ⟨⟨hp, hq⟩, hcross⟩ := hpq
      rw [hAimage] at hp hq
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hq
      refine ⟨(P, Q), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
      exact ⟨⟨hP, hQ⟩, (crosses_map_iff
        (fun i => (pairing.eraseZeroOrderIso i : Fin (2 * (n + 1))))
        pairing.eraseZeroOrderIso.strictMono P.1 P.2 Q.1 Q.2).1 hcross⟩
  rw [hsum', ← hAcross, Pairing.crossingCount, hbij]
  omega

/-- The number of positions strictly between `0` and its partner. -/
def Pairing.interveningPositionCount {n : ℕ} (pairing : Pairing (n + 1)) : ℕ :=
  (pairing.partner 0).val - 1

/-- `crossingsWithFirstPair` and `interveningPositionCount` agree modulo two. -/
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
      · rw [pairing.partner_partner]
        exact hklt
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
      · rw [pairing.partner_partner]
        exact hklt
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

end Combinatorics
