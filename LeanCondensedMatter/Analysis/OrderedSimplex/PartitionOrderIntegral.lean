import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffle
import LeanCondensedMatter.Combinatorics.FinpartitionOrderShuffle

set_option linter.style.header false

/-!
# Ordered-simplex integral sums over finite-partition orders

A global order decomposes into part-local orders and an order-preserving shuffle.
When the global integrand agrees with the shuffled product of the local integrands,
summing its ordered-simplex integral over all global orders gives the product of
the corresponding local order sums. Regularity is required only of local integrands.
-/

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- Sum the ordered-simplex integrals over every order of a finite set by factoring
through a finite partition and its part-local order sums. -/
theorem sum_order_orderedSimplexIntegral_eq_prod_sum_partOrders
    (π : Finpartition s) (β : ℝ)
    (globalIntegrand : (Fin s.card ≃ ↥s) → (Fin s.card → ℝ) → ℂ)
    (localIntegrand : ∀ B : π.parts,
      (Fin (B : Finset α).card ≃ ↥(B : Finset α)) →
        (Fin (B : Finset α).card → ℝ) → ℂ)
    (hshuffle : ∀ (orders : π.PartOrders) (shuffle : π.PartShuffle),
      globalIntegrand (π.assembleOrder orders shuffle) =
        shuffle.ambientIntegrand (fun B => localIntegrand B (orders B)))
    (hlocal : ∀ B order, intervalIntegral.MeasurableLocallyBounded
      (localIntegrand B order)) :
    (∑ order : Fin s.card ≃ ↥s,
      intervalIntegral.orderedSimplexIntegral s.card β (globalIntegrand order)) =
      ∏ B : π.parts,
        ∑ order : Fin (B : Finset α).card ≃ ↥(B : Finset α),
          intervalIntegral.orderedSimplexIntegral (B : Finset α).card β
            (localIntegrand B order) := by
  classical
  have hcard : (∑ B : π.parts, (B : Finset α).card) = s.card := by
    rw [Finset.sum_coe_sort]
    exact π.sum_card_parts
  simpa only [one_mul] using
    (π.sum_order_eq_mul_prod_sum_partOrders
      (fun order => intervalIntegral.orderedSimplexIntegral s.card β (globalIntegrand order))
      (fun B order => intervalIntegral.orderedSimplexIntegral (B : Finset α).card β
        (localIntegrand B order))
      (1 : ℂ) (fun orders => by
        simp_rw [hshuffle orders]
        simpa only [one_mul] using
          Combinatorics.FamilySlotShuffleTo.sum_integral_eq_prod
            (fun B : π.parts => (B : Finset α).card) s.card hcard β
            (fun B => localIntegrand B (orders B))
            (fun B => hlocal B (orders B))))

end Finpartition
