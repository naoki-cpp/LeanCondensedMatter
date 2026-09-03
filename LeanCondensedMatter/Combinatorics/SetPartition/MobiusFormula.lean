import LeanCondensedMatter.Combinatorics.SetPartition.Coarsening
import LeanCondensedMatter.Analysis.PowerSeries.Cumulant

set_option linter.style.header false

/-!
# Explicit Möbius formula for finite set partitions

The bottom-to-top Möbius coefficient of a nonempty partition lattice is
`(-1)^(n - 1) * (n - 1)!`. Coarsening equivalence then gives the corresponding formula from an
arbitrary partition to the top, and the existing restriction product gives every interval.
-/

open scoped BigOperators
open IncidenceAlgebra

variable {α : Type*} [DecidableEq α]

namespace Finpartition

private def atomMoment (S : Finset α) : ℂ :=
  if S.card ≤ 1 then 1 else 0

private theorem partitionProduct_atomMoment_bot (S : Finset α) :
    partitionProduct atomMoment (⊥ : Finpartition S) = 1 := by
  classical
  rw [partitionProduct]
  apply Finset.prod_eq_one
  intro B hB
  rw [mem_bot_iff] at hB
  obtain ⟨x, hx, rfl⟩ := hB
  simp [atomMoment]

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
  exact Finset.prod_eq_zero hB (by simp [atomMoment, hlargeB])

private theorem cumulantFromMoment_atomMoment_eq_mu (S : Finset α) :
    cumulantFromMoment atomMoment S = mu ℂ (⊥ : Finpartition S) ⊤ := by
  classical
  rw [cumulantFromMoment,
    Finset.sum_eq_single (⊥ : Finpartition S)
      (fun π _ hπ => by rw [partitionProduct_atomMoment_ne_bot π hπ, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h),
    partitionProduct_atomMoment_bot, mul_one]

private theorem factorial_coeff_one_add_X {β : Type*} (S : Finset β) :
    (S.card.factorial : ℂ) *
        PowerSeries.coeff S.card (1 + PowerSeries.X : PowerSeries ℂ) = atomMoment S := by
  cases hcard : S.card with
  | zero => simp [atomMoment, hcard]
  | succ n =>
    cases n with
    | zero => simp [atomMoment, hcard]
    | succ n => simp [atomMoment, hcard, PowerSeries.coeff_X]

private theorem factorial_coeff_log_one_add_X (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (PowerSeries.logOf (1 + PowerSeries.X : PowerSeries ℂ)) =
      (((-1 : ℤ) ^ (n - 1) * (n - 1).factorial : ℤ) : ℂ) := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ m =>
    rw [PowerSeries.logOf_one_add_X]
    have hderiv := congrArg (PowerSeries.coeff m)
      (PowerSeries.deriv_log (A := ℂ))
    simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_mk] at hderiv
    have hmap : algebraMap ℚ ℂ ((-1 : ℚ) ^ m) = (-1 : ℂ) ^ m := by simp
    rw [hmap] at hderiv
    simp only [Nat.succ_sub_one]
    calc
      ((m + 1).factorial : ℂ) * PowerSeries.coeff (m + 1) (PowerSeries.log ℂ) =
          (m.factorial : ℂ) *
            (PowerSeries.coeff (m + 1) (PowerSeries.log ℂ) * (m + 1 : ℂ)) := by
              rw [Nat.factorial_succ]
              push_cast
              ring
      _ = (m.factorial : ℂ) * (-1 : ℂ) ^ m := by rw [hderiv]
      _ = (((-1 : ℤ) ^ m * m.factorial : ℤ) : ℂ) := by
        push_cast
        ring

private theorem mu_bot_top_complex {S : Finset α} (hS : S ≠ ∅) :
    mu ℂ (⊥ : Finpartition S) ⊤ =
      (((-1 : ℤ) ^ (S.card - 1) * (S.card - 1).factorial : ℤ) : ℂ) := by
  have hcard : S.card ≠ 0 :=
    Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  have hbridge :=
    Combinatorics.factorial_mul_coeff_logOf_eq_cumulantFromMoment
      (Z := (1 + PowerSeries.X : PowerSeries ℂ)) (by simp) hS
  have hmom :
      (fun T : Finset α =>
        (T.card.factorial : ℂ) *
          PowerSeries.coeff T.card (1 + PowerSeries.X : PowerSeries ℂ)) = atomMoment := by
    funext T
    exact factorial_coeff_one_add_X T
  rw [hmom, factorial_coeff_log_one_add_X S.card hcard,
    cumulantFromMoment_atomMoment_eq_mu] at hbridge
  exact hbridge.symm

private theorem intCast_mu_apply {β : Type*} [PartialOrder β] [LocallyFiniteOrder β]
    [DecidableEq β] (x y : β) :
    ((mu ℤ x y : ℤ) : ℂ) = mu ℂ x y := by
  simpa using map_mu_apply (Int.castRingHom ℂ) x y

/-- For a nonempty finite set, the Möbius coefficient from the discrete partition to the
indiscrete partition is `(-1)^(n - 1) (n - 1)!`. -/
theorem mu_bot_top_eq_factorial {S : Finset α} (hS : S ≠ ∅) :
    mu ℤ (⊥ : Finpartition S) ⊤ =
      (-1 : ℤ) ^ (S.card - 1) * (S.card - 1).factorial := by
  apply Int.cast_injective (α := ℂ)
  rw [intCast_mu_apply]
  exact mu_bot_top_complex hS

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
