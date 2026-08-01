import LeanCondensedMatter.Combinatorics.PerfectPairing

set_option linter.style.header false

/-!
# `Pairing.pairs`, decomposed into `firstPair` plus the smaller pairing's pairs

This module exposes the finite-set decomposition underlying the first-pair recursion, so products
over all pairs can be split into the first-pair factor and the transported smaller pairing.
-/

namespace Combinatorics

/-- `pairing.pairs` decomposes into `firstPair` plus the smaller pairing's pairs, pushed forward
along `eraseZeroOrderIso`. -/
theorem Pairing.pairs_eq_insert_firstPair {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.pairs =
      insert pairing.firstPair
        (pairing.eraseZeroPair.pairs.image fun pr =>
          ((pairing.eraseZeroOrderIso pr.1 : Fin (2 * (n + 1))),
            (pairing.eraseZeroOrderIso pr.2 : Fin (2 * (n + 1))))) := by
  ext p
  simp only [Finset.mem_insert, Finset.mem_image]
  constructor
  · intro hp
    by_cases he : p = pairing.firstPair
    · exact Or.inl he
    · right
      obtain ⟨h1, h2⟩ := pairing.mem_pairs_endpoints_mem_deletedPositions hp he
      refine ⟨(pairing.eraseZeroOrderIso.symm ⟨p.1, h1⟩,
        pairing.eraseZeroOrderIso.symm ⟨p.2, h2⟩), ?_, ?_⟩
      · rw [pairing.eraseZeroPair_mem_pairs_iff]
        simpa using hp
      · simp
  · rintro (rfl | ⟨pr, hpr, rfl⟩)
    · exact pairing.firstPair_mem_pairs
    · rw [pairing.eraseZeroPair_mem_pairs_iff] at hpr
      simpa using hpr

/-- A product over `pairing.pairs` splits into the `firstPair` factor times a product over the
smaller pairing's own pairs. -/
theorem Pairing.prod_pairs_eq_firstPair_mul {n : ℕ} {M : Type*} [CommMonoid M]
    (pairing : Pairing (n + 1)) (f : Fin (2 * (n + 1)) × Fin (2 * (n + 1)) → M) :
    ∏ pr ∈ pairing.pairs, f pr =
      f pairing.firstPair *
        ∏ pr ∈ pairing.eraseZeroPair.pairs,
          f ((pairing.eraseZeroOrderIso pr.1 : Fin (2 * (n + 1))),
            (pairing.eraseZeroOrderIso pr.2 : Fin (2 * (n + 1)))) := by
  rw [pairing.pairs_eq_insert_firstPair]
  rw [Finset.prod_insert, Finset.prod_image]
  · intro pr _ pr' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (pairing.eraseZeroOrderIso.injective (Subtype.ext h.1))
      (pairing.eraseZeroOrderIso.injective (Subtype.ext h.2))
  · simp only [Finset.mem_image, not_exists, not_and]
    intro pr _ heq
    have h0 : (pairing.eraseZeroOrderIso pr.1 : Fin (2 * (n + 1))) ≠ 0 :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp
        (pairing.eraseZeroOrderIso pr.1).property).2).1
    apply h0
    rw [Prod.mk.injEq] at heq
    rw [heq.1]
    rfl

end Combinatorics
