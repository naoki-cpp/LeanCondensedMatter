import LeanCondensedMatter.Combinatorics.FinpartitionProduct
import LeanCondensedMatter.Combinatorics.SetPartition.Refinement
import LeanCondensedMatter.Combinatorics.SetPartition.DistinguishedBlock
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Partition.Finpartition

set_option linter.style.header false

/-!
# Finite-set moment transform on the partition lattice

The moment transform only uses finite sums and products, so it is defined over a commutative
semiring. Möbius inversion, which needs additive inverses, lives separately in
`Combinatorics/Cumulant/Inversion.lean`.

`weightedMomentFromCumulant` additionally retains an arbitrary partition-dependent coefficient.
Unit coefficients recover the ordinary moment; arbitrary coefficients do not imply normalization
or the ordinary Möbius-inversion identities.
-/

variable {α R : Type*} [DecidableEq α] [CommSemiring R]

namespace Finpartition

/-- Moment transform of a finite-set cumulant function. -/
noncomputable def momentFromCumulant (κ : Finset α → R) (S : Finset α) : R :=
  ∑ π : Finpartition S, partitionProduct κ π

/-- A moment formed from connected-block weights with one additional
partition-dependent (e.g. fermionic shuffle) factor. -/
noncomputable def weightedMomentFromCumulant
    (partitionWeight : ∀ S : Finset α, Finpartition S → R)
    (κ : Finset α → R) (S : Finset α) : R :=
  ∑ π : Finpartition S, partitionWeight S π * partitionProduct κ π

/-- Unit partition weights recover the ordinary moment transform. -/
theorem weightedMomentFromCumulant_one
    (κ : Finset α → R) (S : Finset α) :
    weightedMomentFromCumulant (fun _ _ => 1) κ S =
      momentFromCumulant κ S := by
  classical
  simp [weightedMomentFromCumulant, momentFromCumulant]


/-- The moment transform is normalized to `1` on the empty set, independently of the input
cumulant value at the empty set. -/
@[simp]
theorem momentFromCumulant_empty (κ : Finset α → R) :
    momentFromCumulant κ ∅ = 1 := by
  classical
  letI : Unique (Finpartition (∅ : Finset α)) :=
    inferInstanceAs (Unique (Finpartition (⊥ : Finset α)))
  rw [momentFromCumulant, Fintype.sum_unique]
  have hparts : (default : Finpartition (∅ : Finset α)).parts = ∅ := by simp
  simp [partitionProduct, hparts]


theorem partitionProduct_distinguishedBlockEquiv_symm
    (κ : Finset α → R) {s : Finset α} {a : α} (ha : a ∈ s)
    (x : Σ B : BlockContaining s a, Finpartition (s \ B.1)) :
    partitionProduct κ ((distinguishedBlockEquiv s a ha).symm x) =
      κ x.1.1 * partitionProduct κ x.2 := by
  classical
  rcases x with ⟨B, Q⟩
  change (∏ C ∈ insert B.1 Q.parts, κ C) =
    κ B.1 * ∏ C ∈ Q.parts, κ C
  rw [Finset.prod_insert]
  intro hB
  have haDiff : a ∈ s \ B.1 := Q.le hB B.2.2
  exact (Finset.mem_sdiff.mp haDiff).2 B.2.2

/-- The moment sum splits by the block containing a distinguished element. -/
theorem momentFromCumulant_eq_sum_blockContaining (κ : Finset α → R)
    {s : Finset α} {a : α} (ha : a ∈ s) :
    momentFromCumulant κ s =
      ∑ B : BlockContaining s a,
        κ B.1 * momentFromCumulant κ (s \ B.1) := by
  classical
  rw [momentFromCumulant, ← Equiv.sum_comp (distinguishedBlockEquiv s a ha).symm,
    Fintype.sum_sigma]
  apply Fintype.sum_congr
  intro B
  simp_rw [partitionProduct_distinguishedBlockEquiv_symm κ ha]
  rw [← Finset.mul_sum]
  rfl


/-- Sum of block products over refinements factors into blockwise moments. -/
theorem sum_Iic_partitionProduct_eq (κ : Finset α → R) {S : Finset α} (π : Finpartition S) :
    (∑ ρ ∈ Finset.Iic π, partitionProduct κ ρ) = partitionProduct (momentFromCumulant κ) π := by
  classical
  have hstep1 : (∑ ρ : {ρ : Finpartition S // ρ ≤ π}, partitionProduct κ ρ.1) =
      ∏ B : π.parts, momentFromCumulant κ (B : Finset α) := by
    rw [← Equiv.sum_comp (refinementsEquivFiberPartitions π).symm
      (fun ρ : {ρ : Finpartition S // ρ ≤ π} => partitionProduct κ ρ.1)]
    have hpt : ∀ Q : ∀ B : π.parts, Finpartition (B : Finset α),
        partitionProduct κ ((refinementsEquivFiberPartitions π).symm Q).1 =
          ∏ B : π.parts, partitionProduct κ (Q B) := fun Q => by
      change partitionProduct κ (π.bind fun B hB => Q ⟨B, hB⟩) = _
      rw [partitionProduct_bind κ π (fun B hB => Q ⟨B, hB⟩), ← Finset.univ_eq_attach]
    simp_rw [hpt]
    have hdist := Finset.prod_univ_sum
      (fun B : π.parts => (Finset.univ : Finset (Finpartition (B : Finset α))))
      (fun B q => partitionProduct κ q)
    rw [Fintype.piFinset_univ] at hdist
    exact hdist.symm
  rw [Finset.sum_subtype (Finset.Iic π)
    (fun ρ => (Finset.mem_Iic : ρ ∈ Finset.Iic π ↔ ρ ≤ π)) (partitionProduct κ),
    hstep1, partitionProduct, Finset.prod_coe_sort π.parts (momentFromCumulant κ)]

end Finpartition
