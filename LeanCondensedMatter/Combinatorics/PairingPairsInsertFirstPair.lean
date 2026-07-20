import LeanCondensedMatter.Combinatorics.PerfectPairing

set_option linter.style.header false

/-!
# `Pairing.pairs`, decomposed into `firstPair` plus the smaller pairing's pairs

The seventh bridging piece toward the general `n`-point Bloch–de Dominicis induction
(`notes/roadmaps/second-quantization.md`'s Phase 9): `PerfectPairing.lean`'s
`crossingCount_eraseZeroPair` already splits `crossingCount` along `firstPair` internally, but never
exposed the underlying `Finset` decomposition of `pairing.pairs` itself as a standalone fact. This
file states and proves it directly, by the same `eraseZeroOrderIso`/
`mem_pairs_endpoints_mem_deletedPositions` reasoning `crossingCount_eraseZeroPair`'s proof already
uses internally — needed so a product over
`pairing.pairs` (not just a crossing count) can be split into the `firstPair` factor times a
product over the smaller pairing's own pairs.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- **`pairing.pairs` decomposes into `firstPair` plus the smaller pairing's pairs, pushed forward
along `eraseZeroOrderIso`**: every pair other than `firstPair` has both endpoints away from `0` and
`pairing.partner 0` (`mem_pairs_endpoints_mem_deletedPositions`), so it is the image of a unique
pair of `pairing.eraseZeroPair.pairs` under `eraseZeroOrderIso` (`eraseZeroPair_mem_pairs_iff`). -/
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

/-- **A product over `pairing.pairs` splits into the `firstPair` factor times a product over the
smaller pairing's own pairs**, pushed forward along `eraseZeroOrderIso` — the form the general
`n`-point induction's product term actually needs. -/
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

end BlochDeDominicis
end Common
end SecondQuantization
