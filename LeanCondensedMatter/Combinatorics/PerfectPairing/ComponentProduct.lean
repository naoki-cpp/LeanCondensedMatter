import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

/-!
# Products along a decomposition of normalized pairing pairs

A decomposition of the normalized pairs of a perfect pairing is an equivalence
`(Σ B, F B) ≃ pairing.NormalizedPair`.  Reindexing a commutative product along such a decomposition
is independent of what the components mean diagrammatically, so the product identity lives at the
pairing level next to the corresponding generic component-crossing decomposition.
-/

namespace Combinatorics

variable {n : ℕ} {ι M : Type*} [Fintype ι]
  {F : ι → Type*} [∀ B, Fintype (F B)] [CommMonoid M]

/-- Reindex a commutative product over normalized pairs as an iterated product over any dependent
component decomposition of those pairs. -/
theorem Pairing.prod_componentDecomposition (pairing : Pairing n)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair)
    (f : pairing.NormalizedPair → M) :
    (∏ pr, f pr) = ∏ B : ι, ∏ pr : F B, f (e ⟨B, pr⟩) := by
  calc
    (∏ pr, f pr) = ∏ x : Σ B : ι, F B, f (e x) :=
      (Equiv.prod_comp e f).symm
    _ = ∏ B : ι, ∏ pr : F B, f (e ⟨B, pr⟩) :=
      Fintype.prod_sigma _

end Combinatorics
