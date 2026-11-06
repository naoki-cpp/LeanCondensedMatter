import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalSourceSign
import LeanCondensedMatter.Combinatorics.Cumulant.Moment
import Mathlib.RingTheory.PowerSeries.Basic

set_option linter.style.header false

/-!
# Finite fermionic external-source cumulants

Purely algebraic signed moment inversion for finite subsets of external
fermion slots. This module deliberately does not import Dyson integrals or
physical Wick-diagram amplitudes: the diagrammatic partition identity is
a separate physical theorem, not an assumption hidden in the definition.
-/

namespace SecondQuantization
namespace Fermionic

open scoped BigOperators

variable {E : ℕ}

/-- A non-top external partition cannot contain the entire ambient source
set as one of its blocks. This strict decrease underpins the recursive
fermionic cumulant inversion, without postulating an unsigned Möbius formula. -/
private theorem externalPartition_part_ssubset_of_ne_top
    {S : Finset (Fin (2 * E))} (π : Finpartition S)
    (hne : π ≠ ⊤) {B : Finset (Fin (2 * E))}
    (hB : B ∈ π.parts) : B ⊂ S := by
  have hsubset : B ⊆ S := π.le hB
  have hproper : B ≠ S := by
    intro hEq
    have htopLe : (⊤ : Finpartition S) ≤ π := by
      intro T hT
      have hT' : T = S :=
        Finset.mem_singleton.mp (Finpartition.parts_top_subset S hT)
      subst T
      exact ⟨B, hB, by simp [hEq]⟩
    exact hne (le_antisymm le_top htopLe)
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hproper⟩

/-- The signed external-source moment transform is injective on normalized
connected-block functions (whose empty-set values agree). In particular,
there is no ambiguity in defining connected source cumulants from physical
moments, provided the signed Dyson partition identity is established.

The proof is triangular on proper external subsets: the one-block term has
sign one, and every other partition uses strictly smaller blocks. It does
not apply ordinary unsigned Möbius inversion to signed partition weights. -/
theorem externalPartitionWeightedMoment_injective
    (κ κ' : Finset (Fin (2 * E)) → PowerSeries ℂ)
    (hEmpty : κ ∅ = κ' ∅)
    (hMoments : ∀ S : Finset (Fin (2 * E)),
      Finpartition.weightedMomentFromCumulant
        (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) κ S =
      Finpartition.weightedMomentFromCumulant
        (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) κ' S) :
    κ = κ' := by
  classical
  funext S
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases hS : S = ∅
  · simpa only [hS] using hEmpty
  · have hprod (π : Finpartition S) (hne : π ≠ ⊤) :
        Finpartition.partitionProduct κ π =
          Finpartition.partitionProduct κ' π := by
      unfold Finpartition.partitionProduct
      apply Finset.prod_congr rfl
      intro B hB
      exact ih B (externalPartition_part_ssubset_of_ne_top π hne hB)
    have hrest :
        (∑ π ∈ (Finset.univ : Finset (Finpartition S)).erase ⊤,
          PowerSeries.C (externalPartitionSourceSign π) *
            Finpartition.partitionProduct κ π) =
        (∑ π ∈ (Finset.univ : Finset (Finpartition S)).erase ⊤,
          PowerSeries.C (externalPartitionSourceSign π) *
            Finpartition.partitionProduct κ' π) := by
      apply Finset.sum_congr rfl
      intro π hπ
      rw [hprod π (Finset.mem_erase.mp hπ).1]
    have hsource := hMoments S
    unfold Finpartition.weightedMomentFromCumulant at hsource
    rw [← Finset.sum_erase_add Finset.univ
      (fun π : Finpartition S =>
        PowerSeries.C (externalPartitionSourceSign π) *
          Finpartition.partitionProduct κ π) (Finset.mem_univ ⊤),
      ← Finset.sum_erase_add Finset.univ
      (fun π : Finpartition S =>
        PowerSeries.C (externalPartitionSourceSign π) *
          Finpartition.partitionProduct κ' π) (Finset.mem_univ ⊤)] at hsource
    rw [hrest] at hsource
    have htop (k : Finset (Fin (2 * E)) → PowerSeries ℂ) :
        PowerSeries.C (externalPartitionSourceSign (⊤ : Finpartition S)) *
          Finpartition.partitionProduct k (⊤ : Finpartition S) = k S := by
      rw [externalPartitionSourceSign_top, Finpartition.partitionProduct_top hS]
      simp
    rw [htop κ, htop κ'] at hsource
    exact add_left_cancel hsource

/-- Finite fermionic source cumulants, defined recursively from the complete
subset moment function. The recursion is along *strict* subset, since only
non-top partitions require values at proper blocks. No Grassmann algebra and
no unjustified ordinary unsigned partition inversion are introduced. -/
noncomputable def externalSubsetSourceCumulantSeries
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ) :
    Finset (Fin (2 * E)) → PowerSeries ℂ := by
  classical
  let wf : WellFounded
      (fun T S : Finset (Fin (2 * E)) => T ⊂ S) := inferInstance
  exact wf.fix (fun S ih =>
    if S = ∅ then 0
    else M S -
      ∑ π : {π : Finpartition S // π ≠ ⊤},
        PowerSeries.C (externalPartitionSourceSign π.1) *
          ∏ B : π.1.parts,
            ih (B : Finset (Fin (2 * E)))
              (externalPartition_part_ssubset_of_ne_top π.1 π.2 B.2))

/-- The recursive source cumulant is normalized to zero on empty insertion
sets. The normalized empty source moment, in contrast, is one. -/
@[simp]
theorem externalSubsetSourceCumulantSeries_empty
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ) :
    externalSubsetSourceCumulantSeries M ∅ = 0 := by
  classical
  unfold externalSubsetSourceCumulantSeries
  rw [WellFounded.fix_eq]
  simp

/-- The defining triangular equation for fermionic source cumulants. -/
theorem externalSubsetSourceCumulantSeries_eq_sub_properPartitions
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ)
    (S : Finset (Fin (2 * E))) (hS : S ≠ ∅) :
    externalSubsetSourceCumulantSeries M S =
      M S -
        ∑ π : {π : Finpartition S // π ≠ ⊤},
          PowerSeries.C (externalPartitionSourceSign π.1) *
            Finpartition.partitionProduct (externalSubsetSourceCumulantSeries M) π.1 := by
  classical
  unfold externalSubsetSourceCumulantSeries
  rw [WellFounded.fix_eq]
  simp only [hS, ite_false]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  apply congrArg (fun z : PowerSeries ℂ =>
    PowerSeries.C (externalPartitionSourceSign π.1) * z)
  change (∏ B : π.1.parts,
      externalSubsetSourceCumulantSeries M (B : Finset (Fin (2 * E)))) =
    Finpartition.partitionProduct (externalSubsetSourceCumulantSeries M) π.1
  exact Finset.prod_coe_sort π.1.parts
    (externalSubsetSourceCumulantSeries M)

/-- The signed source moment transform is inverted by finite subset
recursion, provided the empty moment is one. This supplies an explicit
fermionic cumulant/source convention before any physical n-point theorem.
No assumption about diagram factorization is needed for this algebraic step. -/
theorem externalSubsetSourceCumulantSeries_reconstruct
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ)
    (hEmpty : M ∅ = 1)
    (S : Finset (Fin (2 * E))) :
    Finpartition.weightedMomentFromCumulant
      (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
      (externalSubsetSourceCumulantSeries M) S = M S := by
  classical
  let κ := externalSubsetSourceCumulantSeries M
  by_cases hS : S = ∅
  · subst S
    letI : Unique (Finpartition (∅ : Finset (Fin (2 * E)))) :=
      inferInstanceAs (Unique (Finpartition (⊥ : Finset (Fin (2 * E)))))
    unfold Finpartition.weightedMomentFromCumulant
    rw [Fintype.sum_unique]
    have htop : (default : Finpartition (∅ : Finset (Fin (2 * E)))) = ⊤ :=
      Subsingleton.elim _ _
    rw [htop]
    change PowerSeries.C (externalPartitionSourceSign (⊤ : Finpartition (∅ : Finset (Fin (2 * E))))) *
      Finpartition.partitionProduct (externalSubsetSourceCumulantSeries M) ⊤ = M ∅
    rw [externalPartitionSourceSign_top]
    have hparts : (⊤ : Finpartition (∅ : Finset (Fin (2 * E)))).parts = ∅ := by
      simp [Finpartition.parts_eq_empty_iff]
    simp [Finpartition.partitionProduct, hparts, hEmpty]
  · let f : Finpartition S → PowerSeries ℂ := fun π =>
      PowerSeries.C (externalPartitionSourceSign π) *
        Finpartition.partitionProduct κ π
    have hrest :
        (∑ π ∈ (Finset.univ : Finset (Finpartition S)).erase ⊤, f π) =
          ∑ π : {π : Finpartition S // π ≠ ⊤}, f π.1 := by
      rw [Finset.sum_subtype
        (p := fun π : Finpartition S => π ≠ ⊤)
        ((Finset.univ : Finset (Finpartition S)).erase ⊤)
        (fun π => by simp) f]
    have htop : f (⊤ : Finpartition S) = κ S := by
      change PowerSeries.C (externalPartitionSourceSign (⊤ : Finpartition S)) *
        Finpartition.partitionProduct κ (⊤ : Finpartition S) = κ S
      rw [externalPartitionSourceSign_top, Finpartition.partitionProduct_top hS]
      simp
    have hsum :
        Finpartition.weightedMomentFromCumulant
          (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) κ S =
        (∑ π ∈ (Finset.univ : Finset (Finpartition S)).erase ⊤, f π) + κ S := by
      change (∑ π : Finpartition S, f π) = _
      rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ (⊤ : Finpartition S))]
      rw [htop]
    have hrec := externalSubsetSourceCumulantSeries_eq_sub_properPartitions M S hS
    change κ S = M S -
      ∑ π : {π : Finpartition S // π ≠ ⊤}, f π.1 at hrec
    calc
      Finpartition.weightedMomentFromCumulant
          (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) κ S =
          (∑ π ∈ (Finset.univ : Finset (Finpartition S)).erase ⊤, f π) + κ S := hsum
      _ = (∑ π : {π : Finpartition S // π ≠ ⊤}, f π.1) + κ S := by rw [hrest]
      _ = (∑ π : {π : Finpartition S // π ≠ ⊤}, f π.1) +
            (M S - ∑ π : {π : Finpartition S // π ≠ ⊤}, f π.1) := by rw [hrec]
      _ = M S := by abel


end Fermionic
end SecondQuantization
