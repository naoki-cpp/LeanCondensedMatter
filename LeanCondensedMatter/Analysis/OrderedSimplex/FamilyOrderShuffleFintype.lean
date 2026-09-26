import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffleFintype
import LeanCondensedMatter.Combinatorics.FamilyOrderShuffle

set_option linter.style.header false

/-!
# Ordered-simplex factorization over finite-family orders

A global order on a finite family decomposes into one local order per fiber and an
order-preserving family shuffle. If a global integrand factorizes accordingly on every assembled
order, summing its ordered-simplex integral over all global orders factors into the product of the
corresponding local order sums.
-/

namespace Combinatorics

open intervalIntegral

variable {ι α : Type*} [Fintype ι] [Fintype α]
variable (F : ι → Type*) [∀ i, Fintype (F i)]

/-- File-local classical decidable equality used only to enumerate finite equivalence types. -/
local instance instDecidableEqFamilyOrderAmbient : DecidableEq α := Classical.decEq α

/-- File-local classical decidable equality for the fibers, kept out of public theorem signatures. -/
local instance instDecidableEqFamilyOrderFiber (i : ι) : DecidableEq (F i) :=
  Classical.decEq (F i)

noncomputable section

/-- Sum-product factorization for ordered-simplex integrals indexed by all global orders of a
finite family, under measurable local boundedness.

The hypothesis `hfactor` is the only model-specific input: on an order assembled from local fiber
orders and a family shuffle, the global integrand must be the shuffled product of the local
integrands. -/
theorem sum_orderedSimplexIntegral_eq_prod_localOrderSums_of_measurableLocallyBounded
    (total : ℕ) (hTotal : (∑ i, Fintype.card (F i)) = total)
    (ambientEquiv : α ≃ Σ i, F i) (β : ℝ)
    (globalIntegrand : (Fin total ≃ α) → (Fin total → ℝ) → ℂ)
    (localIntegrand :
      ∀ i, (Fin (Fintype.card (F i)) ≃ F i) →
        (Fin (Fintype.card (F i)) → ℝ) → ℂ)
    (hfactor :
      ∀ (orders : FamilyOrders F)
        (shuffle : FamilySlotShuffleTo (fun i => Fintype.card (F i)) total),
        globalIntegrand (assembleFamilyOrder F ambientEquiv orders shuffle) =
          shuffle.ambientIntegrand (fun i => localIntegrand i (orders i)))
    (hlocal : ∀ i order, MeasurableLocallyBounded (localIntegrand i order)) :
    (∑ order : Fin total ≃ α,
      orderedSimplexIntegral total β (globalIntegrand order)) =
      ∏ i, ∑ order : Fin (Fintype.card (F i)) ≃ F i,
        orderedSimplexIntegral (Fintype.card (F i)) β
          (localIntegrand i order) := by
  classical
  calc
    (∑ order : Fin total ≃ α,
        orderedSimplexIntegral total β (globalIntegrand order)) =
      ∑ x : FamilyOrders F ×
          FamilySlotShuffleTo (fun i => Fintype.card (F i)) total,
        orderedSimplexIntegral total β
          (globalIntegrand (assembleFamilyOrder F ambientEquiv x.1 x.2)) := by
      rw [← Equiv.sum_comp (familyOrderDecompositionEquiv F ambientEquiv).symm]
      rfl
    _ = ∑ orders : FamilyOrders F,
          ∑ shuffle : FamilySlotShuffleTo (fun i => Fintype.card (F i)) total,
            orderedSimplexIntegral total β
              (globalIntegrand (assembleFamilyOrder F ambientEquiv orders shuffle)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ orders : FamilyOrders F,
          ∏ i, orderedSimplexIntegral (Fintype.card (F i)) β
            (localIntegrand i (orders i)) := by
      apply Fintype.sum_congr
      intro orders
      simp_rw [hfactor orders]
      exact
        FamilySlotShuffleTo.sum_integral_eq_prod
          (fun i => Fintype.card (F i)) total hTotal β
          (fun i => localIntegrand i (orders i))
          (fun i => hlocal i (orders i))
    _ = ∏ i, ∑ order : Fin (Fintype.card (F i)) ≃ F i,
          orderedSimplexIntegral (Fintype.card (F i)) β
            (localIntegrand i order) := by
      simpa using
        (Finset.prod_univ_sum
          (fun i : ι =>
            (Finset.univ : Finset (Fin (Fintype.card (F i)) ≃ F i)))
          (fun i order =>
            orderedSimplexIntegral (Fintype.card (F i)) β
              (localIntegrand i order))).symm

/-- Sum-product factorization for continuous local integrands indexed by all global orders of a
finite family. -/
theorem sum_orderedSimplexIntegral_eq_prod_localOrderSums
    (total : ℕ) (hTotal : (∑ i, Fintype.card (F i)) = total)
    (ambientEquiv : α ≃ Σ i, F i) (β : ℝ)
    (globalIntegrand : (Fin total ≃ α) → (Fin total → ℝ) → ℂ)
    (localIntegrand :
      ∀ i, (Fin (Fintype.card (F i)) ≃ F i) →
        (Fin (Fintype.card (F i)) → ℝ) → ℂ)
    (hfactor :
      ∀ (orders : FamilyOrders F)
        (shuffle : FamilySlotShuffleTo (fun i => Fintype.card (F i)) total),
        globalIntegrand (assembleFamilyOrder F ambientEquiv orders shuffle) =
          shuffle.ambientIntegrand (fun i => localIntegrand i (orders i)))
    (hlocal : ∀ i order, Continuous (localIntegrand i order)) :
    (∑ order : Fin total ≃ α,
      orderedSimplexIntegral total β (globalIntegrand order)) =
      ∏ i, ∑ order : Fin (Fintype.card (F i)) ≃ F i,
        orderedSimplexIntegral (Fintype.card (F i)) β
          (localIntegrand i order) :=
  sum_orderedSimplexIntegral_eq_prod_localOrderSums_of_measurableLocallyBounded
    F total hTotal ambientEquiv β globalIntegrand localIntegrand hfactor
    (fun i order => (hlocal i order).measurableLocallyBounded)

end

end Combinatorics
