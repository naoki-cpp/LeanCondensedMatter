import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalSourceSign
import LeanCondensedMatter.Combinatorics.Cumulant.WeightedInversion
import Mathlib.RingTheory.PowerSeries.Basic

set_option linter.style.header false

/-!
# Finite fermionic external-source cumulants

The fermionic source sign specializes the general unit-top weighted
moment–cumulant inversion on finite subsets. The combinatorial inverse
is independent of Wick diagrams and Dyson amplitudes: identifying its
connected contribution with the physical diagram sum requires a separate
signed moment identity.
-/

namespace SecondQuantization
namespace Fermionic

open scoped BigOperators

variable {E : ℕ}

/-- Proper-source vanishing reduces a signed external moment to its
single-block connected contribution. -/
theorem externalPartitionWeightedMoment_eq_of_proper_zero
    (κ : Finset (Fin (2 * E)) → PowerSeries ℂ)
    (S : Finset (Fin (2 * E))) (hS : S ≠ ∅)
    (hzero : ∀ B : Finset (Fin (2 * E)), B ⊂ S → κ B = 0) :
    Finpartition.weightedMomentFromCumulant
        (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) κ S = κ S := by
  exact Finpartition.weightedMomentFromCumulant_eq_of_proper_zero
    (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) κ S hS
    (by simp [externalPartitionSourceSign_top]) hzero

/-- The signed external-source moment transform is injective on
connected functions with equal empty-set values. In particular, actual
diagram cumulants are uniquely determined once their signed partition
moment identity has been proved. -/
theorem externalPartitionWeightedMoment_injective
    (κ κ' : Finset (Fin (2 * E)) → PowerSeries ℂ)
    (hEmpty : κ ∅ = κ' ∅)
    (hMoments : ∀ S : Finset (Fin (2 * E)),
      Finpartition.weightedMomentFromCumulant
        (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) κ S =
      Finpartition.weightedMomentFromCumulant
        (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) κ' S) :
    κ = κ' := by
  exact Finpartition.weightedMomentFromCumulant_injective
    (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
    (fun S => by simp [externalPartitionSourceSign_top])
    κ κ' hEmpty hMoments

/-- Fermionic source cumulants, recursively reconstructed from the complete
subset moment function using the canonical fermionic partition signs.
The empty connected contribution is zero. -/
noncomputable def externalSubsetSourceCumulantSeries
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ) :
    Finset (Fin (2 * E)) → PowerSeries ℂ :=
  Finpartition.weightedCumulantFromMoment
    (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) M

@[simp]
theorem externalSubsetSourceCumulantSeries_empty
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ) :
    externalSubsetSourceCumulantSeries M ∅ = 0 := by
  exact Finpartition.weightedCumulantFromMoment_empty
    (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) M

/-- The defining triangular equation for fermionic source cumulants. -/
theorem externalSubsetSourceCumulantSeries_eq_sub_properPartitions
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ)
    (S : Finset (Fin (2 * E))) (hS : S ≠ ∅) :
    externalSubsetSourceCumulantSeries M S =
      M S -
        ∑ π : {π : Finpartition S // π ≠ ⊤},
          PowerSeries.C (externalPartitionSourceSign π.1) *
            Finpartition.partitionProduct (externalSubsetSourceCumulantSeries M) π.1 := by
  simpa only [externalSubsetSourceCumulantSeries] using
    (Finpartition.weightedCumulantFromMoment_eq_sub_properPartitions
      (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) M S hS)

/-- The normalized signed source moment transform is inverted by finite
subset recursion. No unsigned Möbius inversion is used for fermionic signs. -/
theorem externalSubsetSourceCumulantSeries_reconstruct
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ)
    (hEmpty : M ∅ = 1)
    (S : Finset (Fin (2 * E))) :
    Finpartition.weightedMomentFromCumulant
      (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
      (externalSubsetSourceCumulantSeries M) S = M S := by
  simpa only [externalSubsetSourceCumulantSeries] using
    (Finpartition.weightedMomentFromCumulant_weightedCumulantFromMoment
      (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) M
      (fun S => by simp [externalPartitionSourceSign_top]) hEmpty S)

end Fermionic
end SecondQuantization
