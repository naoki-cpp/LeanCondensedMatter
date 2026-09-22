import LeanCondensedMatter.Combinatorics.Cumulant.Inversion
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Explicit Möbius formula for finite set partitions

The bottom-to-top Möbius coefficient of a nonempty partition lattice is
`(-1)^(n - 1) * (n - 1)!`. The proof is finite and combinatorial: an atomic moment function is
shown directly to be the moment transform of the factorial-sign block weight, and Möbius inversion
then identifies that weight with the bottom-to-top coefficient. Coarsening equivalence gives the
corresponding formula from an arbitrary partition to the top, and restriction factorization gives
every interval.
-/

open scoped BigOperators
open IncidenceAlgebra

variable {α : Type*} [DecidableEq α]

namespace Finpartition

private def atomMomentCard (n : ℕ) : ℤ :=
  if n ≤ 1 then 1 else 0

private def atomCumulantCard (n : ℕ) : ℤ :=
  if n = 0 then 0 else (-1 : ℤ) ^ (n - 1) * (n - 1).factorial

private def atomMoment (S : Finset α) : ℤ :=
  atomMomentCard S.card

private def atomCumulant (S : Finset α) : ℤ :=
  atomCumulantCard S.card

private theorem partitionProduct_atomMoment_bot (S : Finset α) :
    partitionProduct atomMoment (⊥ : Finpartition S) = 1 := by
  classical
  rw [partitionProduct]
  apply Finset.prod_eq_one
  intro B hB
  rw [mem_bot_iff] at hB
  obtain ⟨x, hx, rfl⟩ := hB
  simp [atomMoment, atomMomentCard]

private theorem partitionProduct_atomMoment_ne_bot {S : Finset α} (π : Finpartition S)
    (hπ : π ≠ ⊥) : partitionProduct atomMoment π = 0 := by
  classical
  have hlarge : ∃ B ∈ π.parts, ¬B.card ≤ 1 := by
    by_contra h
    push Not at h
    have hπbot : π ≤ (⊥ : Finpartition S) := by
      intro B hB
      have hB0 : B ≠ ∅ := π.ne_bot hB
      have hBpos : 0 < B.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hB0)
      have hBle : B.card ≤ 1 := h B hB
      have hBcard : B.card = 1 := by omega
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hBcard
      have hxS : x ∈ S := π.le hB (Finset.mem_singleton_self x)
      exact ⟨{x}, mem_bot_iff.mpr ⟨x, hxS, rfl⟩, le_rfl⟩
    exact hπ (le_antisymm hπbot bot_le)
  obtain ⟨B, hB, hlargeB⟩ := hlarge
  rw [partitionProduct]
  exact Finset.prod_eq_zero hB (by simp [atomMoment, atomMomentCard, hlargeB])

private theorem cumulantFromMoment_atomMoment_eq_mu (S : Finset α) :
    cumulantFromMoment atomMoment S = mu ℤ (⊥ : Finpartition S) ⊤ := by
  classical
  rw [cumulantFromMoment,
    Finset.sum_eq_single (⊥ : Finpartition S)
      (fun π _ hπ => by rw [partitionProduct_atomMoment_ne_bot π hπ, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h),
    partitionProduct_atomMoment_bot, mul_one]

private theorem atomCumulantCard_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℤ) * atomCumulantCard (k + 1) * atomMomentCard (n - k)) =
      atomMomentCard (n + 1) := by
  cases n with
  | zero =>
      simp [atomCumulantCard, atomMomentCard]
  | succ n =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hzero :
          (∑ k ∈ Finset.range n,
            (Nat.choose (n + 1) k : ℤ) * atomCumulantCard (k + 1) *
              atomMomentCard (n + 1 - k)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        have hnot : ¬n + 1 - k ≤ 1 := by omega
        simp [atomMomentCard, hnot]
      rw [hzero, zero_add]
      simp [atomCumulantCard, atomMomentCard, Nat.factorial_succ, pow_succ]
      ring

private theorem momentFromAtomCumulant_eq_atomMoment (S : Finset α) :
    momentFromCumulant atomCumulant S = atomMoment S := by
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases hS : S = ∅
  · subst S
    simp [atomMoment, atomMomentCard]
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    rw [momentFromCumulant_eq_sum_blockContaining atomCumulant ha]
    have hsmall : ∀ B : BlockContaining S a,
        momentFromCumulant atomCumulant (S \ B.1) = atomMoment (S \ B.1) := by
      intro B
      exact ih (S \ B.1) (Finset.sdiff_ssubset B.2.1 ⟨a, B.2.2⟩)
    simp_rw [hsmall]
    have hcardDiff : ∀ B : BlockContaining S a,
        (S \ B.1).card = S.card - B.1.card := by
      intro B
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr B.2.1]
    simp_rw [atomCumulant, atomMoment, hcardDiff]
    rw [sum_blockContaining_card S a ha
      (fun j => atomCumulantCard j * atomMomentCard (S.card - j))]
    let n := S.card - 1
    have hcard : S.card = n + 1 := by
      dsimp [n]
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
      omega
    rw [hcard]
    simpa [Nat.add_sub_add_right] using atomCumulantCard_sum n

/-- For a nonempty finite set, the Möbius coefficient from the discrete partition to the
indiscrete partition is `(-1)^(n - 1) (n - 1)!`. -/
theorem mu_bot_top_eq_factorial {S : Finset α} (hS : S ≠ ∅) :
    mu ℤ (⊥ : Finpartition S) ⊤ =
      (-1 : ℤ) ^ (S.card - 1) * (S.card - 1).factorial := by
  have hmoment : momentFromCumulant atomCumulant = atomMoment := by
    funext T
    exact momentFromAtomCumulant_eq_atomMoment T
  have hcard : S.card ≠ 0 :=
    Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  calc
    mu ℤ (⊥ : Finpartition S) ⊤ = cumulantFromMoment atomMoment S :=
      (cumulantFromMoment_atomMoment_eq_mu S).symm
    _ = cumulantFromMoment (momentFromCumulant atomCumulant) S := by rw [hmoment]
    _ = atomCumulant S := cumulantFromMoment_momentFromCumulant atomCumulant hS
    _ = (-1 : ℤ) ^ (S.card - 1) * (S.card - 1).factorial := by
      simp [atomCumulant, atomCumulantCard, hcard]

/-- Total bottom-to-top formula, including the empty partition lattice. -/
theorem mu_bot_top_eq_factorial_ite (S : Finset α) :
    mu ℤ (⊥ : Finpartition S) ⊤ =
      if S = ∅ then 1 else (-1 : ℤ) ^ (S.card - 1) * (S.card - 1).factorial := by
  by_cases hS : S = ∅
  · subst S
    have hbotTop : (⊥ : Finpartition (⊥ : Finset α)) = ⊤ := Subsingleton.elim _ _
    simp [hbotTop]
  · rw [if_neg hS, mu_bot_top_eq_factorial hS]

/-- The Möbius coefficient from a partition to the top is determined by its number of blocks. -/
theorem mu_to_top_eq_factorial {S : Finset α} (π : Finpartition S) (hS : S ≠ ∅) :
    mu ℤ π ⊤ =
      (-1 : ℤ) ^ (π.parts.card - 1) * (π.parts.card - 1).factorial := by
  rw [mu_to_top_eq_mu_bot_top_parts]
  exact mu_bot_top_eq_factorial (π.parts_nonempty hS).ne_empty

/-- Explicit product formula for every interval in a finite set-partition lattice. -/
theorem mu_eq_prod_factorial {S : Finset α} {π σ : Finpartition S} (hπσ : π ≤ σ) :
    mu ℤ π σ =
      ∏ B : σ.parts,
        (-1 : ℤ) ^ ((π.restrict (σ.le B.2)).parts.card - 1) *
          ((π.restrict (σ.le B.2)).parts.card - 1).factorial := by
  rw [mu_eq_prod_restrict (R := ℤ) hπσ]
  apply Fintype.prod_congr
  intro B
  exact mu_to_top_eq_factorial (π.restrict (σ.le B.2)) (σ.ne_bot B.2)

end Finpartition
