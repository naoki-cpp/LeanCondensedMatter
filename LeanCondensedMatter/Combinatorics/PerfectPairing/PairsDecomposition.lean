import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZero

set_option linter.style.header false

/-!
# `Pairing.pairs`, decomposed into `firstPair` plus the smaller pairing's pairs

This module uses the structural residual-pair decomposition from `EraseZero` and
exposes the resulting product decomposition over `pairing.pairs`.
-/

namespace Combinatorics

/-- A product over `pairing.pairs` splits into the `firstPair` factor times a product over the
smaller pairing's own pairs. -/
theorem Pairing.prod_pairs_eq_firstPair_mul {n : ℕ} {M : Type*} [CommMonoid M]
    (pairing : Pairing (n + 1)) (f : Fin (2 * (n + 1)) × Fin (2 * (n + 1)) → M) :
    ∏ pr ∈ pairing.pairs, f pr =
      f pairing.firstPair *
        ∏ pr ∈ pairing.eraseZeroPair.pairs,
          f ((pairing.eraseZeroOrderIso pr.1 : Fin (2 * (n + 1))),
            (pairing.eraseZeroOrderIso pr.2 : Fin (2 * (n + 1)))) := by
  classical
  rw [← Finset.insert_erase pairing.firstPair_mem_pairs,
    pairing.pairs_erase_firstPair_eq_image]
  rw [Finset.prod_insert, Finset.prod_image]
  · intro p _ q _ h
    exact pairing.eraseZeroPairEmbedding.injective h
  · rw [← pairing.pairs_erase_firstPair_eq_image]
    simp

end Combinatorics
