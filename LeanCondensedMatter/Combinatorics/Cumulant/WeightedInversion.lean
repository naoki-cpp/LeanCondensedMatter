import LeanCondensedMatter.Combinatorics.Cumulant.Moment
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# Inversion of a partition-weighted finite-set moment transform

The partition weight is arbitrary except that the single-block partition
has weight one. Thus the transform is triangular in strict subsets, with
unit diagonal, and has a unique inverse once the empty-set moment is fixed.

Unlike ordinary moment–cumulant inversion, this does not use the unsigned
partition-lattice Möbius function: an arbitrary partition-dependent weight
need not be multiplicative under refinement.
-/

open scoped BigOperators

namespace Finpartition

variable {α R : Type*} [DecidableEq α] [CommRing R]

/-- Every block of a non-top partition is a strict subset of its support. -/
private theorem part_ssubset_of_ne_top
    {S : Finset α} (π : Finpartition S)
    (hne : π ≠ ⊤) {B : Finset α}
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

/-- The top partition contributes precisely the connected weight;
all other partitions involve proper subsets. -/
theorem weightedMomentFromCumulant_eq_sum_proper_add_top
    (w : ∀ S : Finset α, Finpartition S → R)
    (κ : Finset α → R)
    (S : Finset α) (hS : S ≠ ∅)
    (hTop : w S ⊤ = 1) :
    weightedMomentFromCumulant w κ S =
      (∑ π : {π : Finpartition S // π ≠ ⊤},
        w S π.1 * partitionProduct κ π.1) + κ S := by
  classical
  let f : Finpartition S → R := fun π => w S π * partitionProduct κ π
  change (∑ π : Finpartition S, f π) = _
  rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ (⊤ : Finpartition S))]
  have htop : f (⊤ : Finpartition S) = κ S := by
    change w S ⊤ * partitionProduct κ (⊤ : Finpartition S) = κ S
    rw [hTop, partitionProduct_top hS]
    simp
  rw [htop]
  rw [Finset.sum_subtype
    (p := fun π : Finpartition S => π ≠ ⊤)
    ((Finset.univ : Finset (Finpartition S)).erase ⊤)
    (fun π => by simp) f]

/-- Vanishing on all proper subsets reduces a weighted moment to its top term. -/
theorem weightedMomentFromCumulant_eq_of_proper_zero
    (w : ∀ S : Finset α, Finpartition S → R)
    (κ : Finset α → R)
    (S : Finset α) (hS : S ≠ ∅)
    (hTop : w S ⊤ = 1)
    (hzero : ∀ B : Finset α, B ⊂ S → κ B = 0) :
    weightedMomentFromCumulant w κ S = κ S := by
  classical
  rw [weightedMomentFromCumulant_eq_sum_proper_add_top w κ S hS hTop]
  have hrest :
      (∑ π : {π : Finpartition S // π ≠ ⊤},
        w S π.1 * partitionProduct κ π.1) = 0 := by
    apply Finset.sum_eq_zero
    intro π _
    obtain ⟨B, hB⟩ := (Finpartition.parts_nonempty_iff (P := π.1)).2 hS
    have hproper : B ⊂ S := part_ssubset_of_ne_top π.1 π.2 hB
    have hprod : partitionProduct κ π.1 = 0 := by
      unfold partitionProduct
      exact Finset.prod_eq_zero hB (hzero B hproper)
    rw [hprod, mul_zero]
  rw [hrest, zero_add]

/-- A unit-top weighted moment transform is injective on connected
set functions whose empty-set values agree. -/
theorem weightedMomentFromCumulant_injective
    (w : ∀ S : Finset α, Finpartition S → R)
    (hTop : ∀ S : Finset α, w S ⊤ = 1)
    (κ κ' : Finset α → R)
    (hEmpty : κ ∅ = κ' ∅)
    (hMoments : ∀ S : Finset α,
      weightedMomentFromCumulant w κ S =
        weightedMomentFromCumulant w κ' S) :
    κ = κ' := by
  classical
  funext S
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases hS : S = ∅
  · simpa only [hS] using hEmpty
  · have hprod (π : Finpartition S) (hne : π ≠ ⊤) :
        partitionProduct κ π = partitionProduct κ' π := by
      unfold partitionProduct
      apply Finset.prod_congr rfl
      intro B hB
      exact ih B (part_ssubset_of_ne_top π hne hB)
    have hrest :
        (∑ π : {π : Finpartition S // π ≠ ⊤},
          w S π.1 * partitionProduct κ π.1) =
        (∑ π : {π : Finpartition S // π ≠ ⊤},
          w S π.1 * partitionProduct κ' π.1) := by
      apply Finset.sum_congr rfl
      intro π _
      rw [hprod π.1 π.2]
    have hsource := hMoments S
    rw [weightedMomentFromCumulant_eq_sum_proper_add_top w κ S hS (hTop S),
      weightedMomentFromCumulant_eq_sum_proper_add_top w κ' S hS (hTop S)] at hsource
    rw [hrest] at hsource
    exact add_left_cancel hsource

/-- Recursive inverse of a unit-top partition-weighted moment transform.
The empty-set connected contribution is set to zero; the corresponding
moment is determined by the empty-partition weight. -/
noncomputable def weightedCumulantFromMoment
    (w : ∀ S : Finset α, Finpartition S → R)
    (M : Finset α → R) : Finset α → R := by
  classical
  let wf : WellFounded (fun T S : Finset α => T ⊂ S) := inferInstance
  exact wf.fix (fun S ih =>
    if S = ∅ then 0
    else M S -
      ∑ π : {π : Finpartition S // π ≠ ⊤},
        w S π.1 *
          ∏ B : π.1.parts,
            ih (B : Finset α) (part_ssubset_of_ne_top π.1 π.2 B.2))

@[simp]
theorem weightedCumulantFromMoment_empty
    (w : ∀ S : Finset α, Finpartition S → R)
    (M : Finset α → R) :
    weightedCumulantFromMoment w M ∅ = 0 := by
  classical
  unfold weightedCumulantFromMoment
  rw [WellFounded.fix_eq]
  simp

/-- The recursive inverse is the moment minus its proper-partition terms. -/
theorem weightedCumulantFromMoment_eq_sub_properPartitions
    (w : ∀ S : Finset α, Finpartition S → R)
    (M : Finset α → R)
    (S : Finset α) (hS : S ≠ ∅) :
    weightedCumulantFromMoment w M S =
      M S -
        ∑ π : {π : Finpartition S // π ≠ ⊤},
          w S π.1 *
            partitionProduct (weightedCumulantFromMoment w M) π.1 := by
  classical
  unfold weightedCumulantFromMoment
  rw [WellFounded.fix_eq]
  simp only [hS, ite_false]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  apply congrArg (fun z : R => w S π.1 * z)
  change (∏ B : π.1.parts,
      weightedCumulantFromMoment w M (B : Finset α)) =
    partitionProduct (weightedCumulantFromMoment w M) π.1
  exact Finset.prod_coe_sort π.1.parts (weightedCumulantFromMoment w M)

/-- A unit-top weighted moment transform reconstructs the original
normalized moments from its recursively defined connected weights. -/
theorem weightedMomentFromCumulant_weightedCumulantFromMoment
    (w : ∀ S : Finset α, Finpartition S → R)
    (M : Finset α → R)
    (hTop : ∀ S : Finset α, w S ⊤ = 1)
    (hEmpty : M ∅ = 1)
    (S : Finset α) :
    weightedMomentFromCumulant w (weightedCumulantFromMoment w M) S = M S := by
  classical
  let κ := weightedCumulantFromMoment w M
  by_cases hS : S = ∅
  · subst S
    rw [weightedMomentFromCumulant_empty, hTop]
    exact hEmpty.symm
  · have hrec := weightedCumulantFromMoment_eq_sub_properPartitions w M S hS
    change κ S = M S -
      ∑ π : {π : Finpartition S // π ≠ ⊤},
        w S π.1 * partitionProduct κ π.1 at hrec
    rw [weightedMomentFromCumulant_eq_sum_proper_add_top w κ S hS (hTop S)]
    rw [hrec]
    abel

end Finpartition
