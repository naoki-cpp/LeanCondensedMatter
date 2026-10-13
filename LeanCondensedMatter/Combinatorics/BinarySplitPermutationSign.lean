import LeanCondensedMatter.Combinatorics.FamilySlotShuffleSign

set_option linter.style.header false

/-!
# Relative signs of binary order-preserving position splits

A binary split of finite positions is a two-block family shuffle when the
two local embeddings are increasing. Reuse the general relative-family-shuffle
sign theorem rather than computing a second permutation inversion formula.
-/

namespace Combinatorics

open scoped BigOperators

private def binaryBlockTagEquiv (m n : ℕ) :
    (Σ b : Bool, Fin (if b then n else m)) ≃ Fin m ⊕ Fin n where
  toFun
    | ⟨false, p⟩ => Sum.inl p
    | ⟨true, p⟩ => Sum.inr p
  invFun
    | Sum.inl p => ⟨false, p⟩
    | Sum.inr p => ⟨true, p⟩
  left_inv := by
    rintro ⟨b, p⟩
    cases b <;> rfl
  right_inv := by
    rintro (p | p) <;> rfl

private def binaryBlockOrder : Bool ≃ Fin (Fintype.card Bool) where
  toFun b := if b then 1 else 0
  invFun p := p = 1
  left_inv b := by
    cases b <;> decide
  right_inv p := by
    fin_cases p <;> decide

private noncomputable def binaryBlockShuffle {m n total : ℕ}
    (e : Fin m ⊕ Fin n ≃ Fin total)
    (hleft : StrictMono (fun i : Fin m => e (Sum.inl i)))
    (hright : StrictMono (fun j : Fin n => e (Sum.inr j))) :
    FamilySlotShuffleTo (fun b : Bool => if b then n else m) total where
  slotEquiv := (binaryBlockTagEquiv m n).trans e
  strictMono := by
    intro b
    cases b with
    | false => simpa [binaryBlockTagEquiv] using hleft
    | true => simpa [binaryBlockTagEquiv] using hright

private theorem binaryBlockShuffle_orderedBlockInversionCount
    {m n total : ℕ} (e : Fin m ⊕ Fin n ≃ Fin total)
    (hleft : StrictMono (fun i : Fin m => e (Sum.inl i)))
    (hright : StrictMono (fun j : Fin n => e (Sum.inr j))) :
    (binaryBlockShuffle e hleft hright).orderedBlockInversionCount
        binaryBlockOrder =
      ∑ i : Fin m, ∑ j : Fin n,
        if e (Sum.inr j) < e (Sum.inl i) then 1 else 0 := by
  classical
  let s := binaryBlockShuffle e hleft hright
  have hbool : s.orderedBlockInversionCount binaryBlockOrder =
      s.blockInversionCount false true := by
    simp [FamilySlotShuffleTo.orderedBlockInversionCount,
      Finset.offDiag, binaryBlockOrder]
  change s.orderedBlockInversionCount binaryBlockOrder = _
  rw [hbool, FamilySlotShuffleTo.blockInversionCount_of_ne (by decide)]
  rfl

/-- For two order-preserving splittings of the same ambient finite positions,
the sign of the relative permutation is the sum of their respective
right-before-left inter-sector position-inversion counts, modulo two. -/
theorem sign_relative_binarySplittings_eq_inversionCounts
    {m n total : ℕ}
    (fixed mixed : Fin m ⊕ Fin n ≃ Fin total)
    (hfixedLeft : StrictMono (fun i : Fin m => fixed (Sum.inl i)))
    (hfixedRight : StrictMono (fun j : Fin n => fixed (Sum.inr j)))
    (hmixedLeft : StrictMono (fun i : Fin m => mixed (Sum.inl i)))
    (hmixedRight : StrictMono (fun j : Fin n => mixed (Sum.inr j))) :
    Equiv.Perm.sign (fixed.symm.trans mixed) =
      (-1 : ℤˣ) ^
        ((∑ i : Fin m, ∑ j : Fin n,
            if fixed (Sum.inr j) < fixed (Sum.inl i) then 1 else 0) +
          (∑ i : Fin m, ∑ j : Fin n,
            if mixed (Sum.inr j) < mixed (Sum.inl i) then 1 else 0)) := by
  let s := binaryBlockShuffle fixed hfixedLeft hfixedRight
  let t := binaryBlockShuffle mixed hmixedLeft hmixedRight
  have hrelative : s.relativePerm t = fixed.symm.trans mixed := by
    apply Equiv.ext
    intro p
    change mixed ((binaryBlockTagEquiv m n)
      ((binaryBlockTagEquiv m n).symm (fixed.symm p))) =
        mixed (fixed.symm p)
    simp
  have hsign :=
    FamilySlotShuffleTo.relativePerm_sign_eq_orderedBlockInversionCount_add
      s t binaryBlockOrder
  rw [hrelative,
    binaryBlockShuffle_orderedBlockInversionCount fixed hfixedLeft hfixedRight,
    binaryBlockShuffle_orderedBlockInversionCount mixed hmixedLeft hmixedRight] at hsign
  exact hsign

end Combinatorics
