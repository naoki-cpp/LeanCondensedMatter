import LeanCondensedMatter.Combinatorics.SetPartition.DistinguishedBlock
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Stirling enumeration of finite set partitions

Finite partitions of a finite set with exactly `k` blocks are counted by the Stirling number of
the second kind.  The proof uses the distinguished-block decomposition and the standard Stirling
recurrence, and is independent of incidence-algebra or Möbius-inversion machinery.
-/

namespace Finpartition

variable {α : Type*} [DecidableEq α]

private theorem sum_choose_mul_stirlingSecond (n k : ℕ) :
    (∑ i ∈ Finset.range (n + 1), n.choose i * Nat.stirlingSecond i k) =
      Nat.stirlingSecond (n + 1) (k + 1) := by
  induction n with
  | zero =>
      cases k <;> simp
  | succ n ih =>
      cases k with
      | zero =>
          simp [Nat.stirlingSecond_one_right]
      | succ k =>
          rw [Finset.sum_range_succ'
            (fun i => (n + 1).choose i * Nat.stirlingSecond i (k + 1)) (n + 1)]
          simp only [Nat.choose_zero_right, Nat.stirlingSecond_zero_succ, mul_zero, zero_add]
          simp_rw [Nat.choose_succ_succ', Nat.stirlingSecond_succ_succ]
          have hshift :
              (∑ i ∈ Finset.range (n + 1),
                  n.choose (i + 1) * Nat.stirlingSecond (i + 1) (k + 1)) =
                ∑ i ∈ Finset.range (n + 1),
                  n.choose i * Nat.stirlingSecond i (k + 1) := by
            rw [Finset.sum_range_succ
                (fun i => n.choose (i + 1) * Nat.stirlingSecond (i + 1) (k + 1)),
              Finset.sum_range_succ'
                (fun i => n.choose i * Nat.stirlingSecond i (k + 1)) n]
            simp
          have hrec :
              (∑ i ∈ Finset.range (n + 1),
                  n.choose i * Nat.stirlingSecond (i + 1) (k + 1)) =
                (k + 1) *
                    (∑ i ∈ Finset.range (n + 1),
                      n.choose i * Nat.stirlingSecond i (k + 1)) +
                  ∑ i ∈ Finset.range (n + 1),
                    n.choose i * Nat.stirlingSecond i k := by
            simp_rw [Nat.stirlingSecond_succ_succ, mul_add]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            apply congrArg₂ (· + ·)
            · apply Finset.sum_congr rfl
              intro i hi
              ring
            · rfl
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib, hrec, hshift, ih (k + 1), ih k]
          rw [Nat.stirlingSecond_succ_succ]
          ring

private theorem sum_choose_mul_stirlingSecond_complement (n k : ℕ) :
    (∑ i ∈ Finset.range (n + 1), n.choose i * Nat.stirlingSecond (n - i) k) =
      Nat.stirlingSecond (n + 1) (k + 1) := by
  rw [← Finset.sum_range_reflect]
  have h :
      (∑ i ∈ Finset.range (n + 1),
          n.choose (n - i) * Nat.stirlingSecond (n - (n - i)) k) =
        ∑ i ∈ Finset.range (n + 1), n.choose i * Nat.stirlingSecond i k := by
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    rw [Nat.choose_symm hin, Nat.sub_sub_cancel hin]
  rw [h]
  exact sum_choose_mul_stirlingSecond n k

private theorem card_parts_distinguishedBlockEquiv_symm
    {s : Finset α} {a : α} (ha : a ∈ s)
    (x : Σ B : BlockContaining s a, Finpartition (s \ B.1)) :
    ((distinguishedBlockEquiv s a ha).symm x).parts.card = x.2.parts.card + 1 := by
  rcases x with ⟨B, Q⟩
  change
    (Q.extend (Finset.ne_empty_of_mem B.2.2) disjoint_sdiff_self_left
      (Finset.sdiff_union_of_subset B.2.1)).parts.card = Q.parts.card + 1
  exact card_extend Q B.1 s

private def subtypeSigmaSndEquiv {ι : Type*} {β : ι → Type*}
    (q : (i : ι) → β i → Prop) :
    {x : Σ i, β i // q x.1 x.2} ≃ Σ i, {b : β i // q i b} where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := by
    rcases x with ⟨⟨i, b⟩, hb⟩
    rfl
  right_inv x := by
    rcases x with ⟨i, ⟨b, hb⟩⟩
    rfl

private def partsCardSuccEquiv
    {s : Finset α} {a : α} (ha : a ∈ s) (k : ℕ) :
    {P : Finpartition s // P.parts.card = k + 1} ≃
      Σ B : BlockContaining s a,
        {Q : Finpartition (s \ B.1) // Q.parts.card = k} := by
  let e := distinguishedBlockEquiv s a ha
  refine (Equiv.subtypeEquiv e ?_).trans
    (subtypeSigmaSndEquiv
      (fun B : BlockContaining s a => fun Q : Finpartition (s \ B.1) => Q.parts.card = k))
  intro P
  have hcard : P.parts.card = (e P).2.parts.card + 1 := by
    simpa [e] using card_parts_distinguishedBlockEquiv_symm ha (e P)
  omega

/-- Finite partitions with exactly `k` blocks are counted by the Stirling number of the second
kind. -/
theorem card_parts_eq_stirlingSecond (s : Finset α) (k : ℕ) :
    Fintype.card {P : Finpartition s // P.parts.card = k} =
      Nat.stirlingSecond s.card k := by
  classical
  induction s using Finset.strongInductionOn generalizing k with
  | h s ih =>
      by_cases hs : s = ∅
      · subst s
        cases k with
        | zero =>
            letI : Unique (Finpartition (∅ : Finset α)) :=
              inferInstanceAs (Unique (Finpartition (⊥ : Finset α)))
            letI : Unique {P : Finpartition (∅ : Finset α) // P.parts.card = 0} where
              default := ⟨default, by simp⟩
              uniq P := by
                apply Subtype.ext
                exact Subsingleton.elim _ _
            simp [Nat.stirlingSecond]
        | succ k =>
            simp only [Nat.stirlingSecond_zero_succ]
            rw [Fintype.card_eq_zero_iff]
            exact ⟨fun P => by
              have hparts : P.1.parts = ∅ :=
                (Finpartition.parts_eq_empty_iff (P := P.1)).2 rfl
              simp [hparts] at P.2⟩
      · cases k with
        | zero =>
            have hpos : 0 < s.card :=
              Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
            have hcard : s.card = (s.card - 1) + 1 := by omega
            rw [hcard, Nat.stirlingSecond_succ_zero, Fintype.card_eq_zero_iff]
            exact ⟨fun P => by
              have hne : P.1.parts.Nonempty := P.1.parts_nonempty hs
              exact (Finset.card_ne_zero.mpr hne) P.2⟩
        | succ k =>
            obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
            rw [Fintype.card_congr (partsCardSuccEquiv ha k), Fintype.card_sigma]
            have hsmall : ∀ B : BlockContaining s a,
                Fintype.card
                    {Q : Finpartition (s \ B.1) // Q.parts.card = k} =
                  Nat.stirlingSecond (s \ B.1).card k := by
              intro B
              exact ih (s \ B.1) (Finset.sdiff_ssubset B.2.1 ⟨a, B.2.2⟩) k
            simp_rw [hsmall]
            calc
              (∑ B : BlockContaining s a, Nat.stirlingSecond (s \ B.1).card k) =
                  ∑ B : BlockContaining s a,
                    Nat.stirlingSecond (s.card - B.1.card) k := by
                    apply Fintype.sum_congr
                    intro B
                    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr B.2.1]
              _ = ∑ j ∈ Finset.range s.card,
                    (s.card - 1).choose j *
                      Nat.stirlingSecond (s.card - (j + 1)) k := by
                    exact sum_blockContaining_card s a ha
                      (fun b => Nat.stirlingSecond (s.card - b) k)
              _ = Nat.stirlingSecond s.card (k + 1) := by
                    have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
                    have hcard : s.card = (s.card - 1) + 1 := by omega
                    simpa [hcard, Nat.add_sub_add_right] using
                      sum_choose_mul_stirlingSecond_complement (s.card - 1) k

end Finpartition
