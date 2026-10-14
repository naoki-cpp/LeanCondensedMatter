import LeanCondensedMatter.Combinatorics.BinarySplitPermutationSign
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.SlotSplitMixedOrder

set_option linter.style.header false

/-!
# Permutation signs for external-support and vacuum slot splitting

The support is ordered in its own mixed-time coordinates. On explicitly ordered
vacuum chambers, the ambient permutation sign cancels the inter-sector inversion
sign, leaving the support permutation sign. These identities do not use labels,
thermal kernels, or a choice of particle statistics.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- The relative permutation between the fixed and mixed atomic support/vacuum
splittings carries the full mixed-time ordering sign and the actual
external-support local reordering sign. No order-preservation assumption
is made about the external support in its original flattened order.
The vacuum local order is the identity in this comparison. -/
private theorem externalInsertionMixedSplit_relativePerm_sign_eq_local_mul_global
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let localFixed := (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).symm
    let fixedSplit :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (finCongr (by simp)).symm
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let mixedSplit :=
      (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split
    Equiv.Perm.sign (fixedSplit.symm.trans mixedSplit) =
      Equiv.Perm.sign
          (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))) *
        Equiv.Perm.sign
          (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) := by
  intro S order localFixed fixedSplit split mixedSplit
  let localPerm : Equiv.Perm
      (Fin (2 * (2 * T.card + E)) ⊕ Fin (2 * (2 * S.card))) :=
    Equiv.sumCongr localFixed (Equiv.refl _)
  let globalPerm : Equiv.Perm (Fin (2 * (2 * n + E))) :=
    externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ
  have hsplit : split = fixedSplit.trans globalPerm := by
    apply Equiv.ext
    intro p
    rfl
  have hrelative :
      fixedSplit.symm.trans mixedSplit =
        (fixedSplit.symm.trans (localPerm.trans fixedSplit)).trans globalPerm := by
    rw [show mixedSplit = localPerm.trans split from rfl, hsplit]
    apply Equiv.ext
    intro p
    rfl
  have hassoc :
      fixedSplit.symm.trans (localPerm.trans fixedSplit) =
        (fixedSplit.symm.trans localPerm).trans fixedSplit := by
    apply Equiv.ext
    intro p
    rfl
  rw [hrelative, Equiv.Perm.sign_trans, hassoc,
    Equiv.Perm.sign_symm_trans_trans]
  exact mul_comm _ _

/-- The relative fixed/mixed support split sign is determined by the two
inter-sector inversion counts on strictly antitone vacuum time chambers.
Both fixed-sector embeddings are now shown to preserve the canonical flattened
order; the parity of the fixed inter-sector inversion count remains separate. -/
private theorem externalInsertionMixedSplit_relativePerm_sign_eq_inversionCounts
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let localFixed := (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).symm
    let fixedSplit :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (finCongr (by simp)).symm
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let mixedSplit :=
      (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split
    StrictAnti (σ ∘ f) →
    Equiv.Perm.sign (fixedSplit.symm.trans mixedSplit) =
      (-1 : ℤˣ) ^
        ((∑ i : Fin (2 * (2 * T.card + E)),
            ∑ j : Fin (2 * (2 * S.card)),
              if fixedSplit (Sum.inr j) < fixedSplit (Sum.inl i) then 1 else 0) +
          (∑ i : Fin (2 * (2 * T.card + E)),
            ∑ j : Fin (2 * (2 * S.card)),
              if mixedSplit (Sum.inr j) < mixedSplit (Sum.inl i) then 1 else 0)) := by
  intro S order f localFixed fixedSplit split mixedSplit htime
  have hfixedLeft : StrictMono
      (fun i : Fin (2 * (2 * T.card + E)) => fixedSplit (Sum.inl i)) := by
    intro a b hab
    have hleft :=
      externalInsertionSlotLegSplitting_left_strictMono (E := E) T hab
    change (Fin.cast (by simp)
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl a))).val <
      (Fin.cast (by simp)
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl b))).val
    simpa only [Fin.val_cast, Fin.lt_def] using hleft
  have hfixedRight : StrictMono
      (fun j : Fin (2 * (2 * S.card)) => fixedSplit (Sum.inr j)) := by
    intro a b hab
    have hright :=
      externalInsertionSlotLegSplitting_orderedRight_strictMono (E := E) T hab
    change (Fin.cast (by simp)
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inr (orderedLegToDiagramLeg S order a)))).val <
      (Fin.cast (by simp)
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inr (orderedLegToDiagramLeg S order b)))).val
    simpa only [Fin.val_cast, Fin.lt_def] using hright
  have hmixedLeft : StrictMono
      (fun i : Fin (2 * (2 * T.card + E)) => mixedSplit (Sum.inl i)) :=
    externalInsertionLeftMixedPosition_split_strictMono T externalTime σ
  have hright0 :=
    externalInsertionSlotLegSplitting_right_strictMono_of_localOrder T externalTime σ
      (externalInsertionMixedTimeOrderedAtomicLegPosition_zero_strictMono_of_strictAnti
        (σ ∘ f) htime)
  have hmixedRight : StrictMono
      (fun j : Fin (2 * (2 * S.card)) => mixedSplit (Sum.inr j)) := by
    simpa only [mixedSplit, split, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.refl_apply] using hright0
  exact sign_relative_binarySplittings_eq_inversionCounts
    fixedSplit mixedSplit hfixedLeft hfixedRight hmixedLeft hmixedRight

/-- On a strictly antitone vacuum chamber, the relative fixed/mixed split sign
depends only on mixed-time inter-sector inversions. The fixed-order inversions
are even because vacuum vertices occur as complete four-leg blocks. -/
private theorem externalInsertionMixedSplit_relativePerm_sign_eq_mixedInversionCount
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let localFixed := (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).symm
    let fixedSplit :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (finCongr (by simp)).symm
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let mixedSplit :=
      (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split
    StrictAnti (σ ∘ f) →
    Equiv.Perm.sign (fixedSplit.symm.trans mixedSplit) =
      (-1 : ℤˣ) ^
        (∑ i : Fin (2 * (2 * T.card + E)),
          ∑ j : Fin (2 * (2 * S.card)),
            if mixedSplit (Sum.inr j) < mixedSplit (Sum.inl i) then 1 else 0) := by
  intro S order f localFixed fixedSplit split mixedSplit htime
  let fixedCount : ℕ :=
    ∑ i : Fin (2 * (2 * T.card + E)),
      ∑ j : Fin (2 * (2 * S.card)),
        if fixedSplit (Sum.inr j) < fixedSplit (Sum.inl i) then 1 else 0
  let mixedCount : ℕ :=
    ∑ i : Fin (2 * (2 * T.card + E)),
      ∑ j : Fin (2 * (2 * S.card)),
        if mixedSplit (Sum.inr j) < mixedSplit (Sum.inl i) then 1 else 0
  change Equiv.Perm.sign (fixedSplit.symm.trans mixedSplit) =
    (-1 : ℤˣ) ^ mixedCount
  have hfixed : fixedCount % 2 = 0 := by
    change (∑ i : Fin (2 * (2 * T.card + E)),
      ∑ j : Fin (2 * (2 * S.card)),
        if (Fin.cast (by simp)
              (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
                (Sum.inr (orderedLegToDiagramLeg S order j)))).val <
            (Fin.cast (by simp)
              (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
                (Sum.inl i))).val
        then 1 else 0) % 2 = 0
    simpa only [Fin.lt_def, Fin.val_cast] using
      (externalInsertionSlotLegSplitting_fixedInversionCount_mod_two_eq_zero (E := E) T)
  have hcounts : Equiv.Perm.sign (fixedSplit.symm.trans mixedSplit) =
      (-1 : ℤˣ) ^ (fixedCount + mixedCount) :=
    externalInsertionMixedSplit_relativePerm_sign_eq_inversionCounts
      T externalTime σ htime
  rw [hcounts, pow_add, Int.units_pow_eq_pow_mod_two (-1 : ℤˣ) fixedCount, hfixed]
  simp

/-- The product of the genuine local external-support reordering sign and the
ambient fixed-to-mixed atomic ordering sign equals the inter-sector inversion
sign. The fixed-order support/vacuum inversions have already been proved even,
so no fixed-split correction or internal monotonicity hypothesis remains. -/
private theorem externalInsertionMixedSplit_local_mul_global_sign_eq_mixedInversionCount
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let localFixed := (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).symm
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let mixedSplit :=
      (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split
    StrictAnti (σ ∘ f) →
    Equiv.Perm.sign
        (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))) *
      Equiv.Perm.sign
        (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) =
      (-1 : ℤˣ) ^
        (∑ i : Fin (2 * (2 * T.card + E)),
          ∑ j : Fin (2 * (2 * S.card)),
            if mixedSplit (Sum.inr j) < mixedSplit (Sum.inl i) then 1 else 0) := by
  intro S order f localFixed split mixedSplit htime
  let fixedSplit :
      (Fin (2 * (2 * T.card + E)) ⊕ Fin (2 * (2 * S.card))) ≃
        Fin (2 * (2 * n + E)) :=
    ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
      (orderedLegToDiagramLeg S order)).trans
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
      (finCongr (by simp)).symm
  calc
    Equiv.Perm.sign
          (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))) *
        Equiv.Perm.sign
          (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) =
        Equiv.Perm.sign (fixedSplit.symm.trans mixedSplit) := by
          exact (externalInsertionMixedSplit_relativePerm_sign_eq_local_mul_global
            T externalTime σ).symm
    _ = (-1 : ℤˣ) ^
          (∑ i : Fin (2 * (2 * T.card + E)),
            ∑ j : Fin (2 * (2 * S.card)),
              if mixedSplit (Sum.inr j) < mixedSplit (Sum.inl i) then 1 else 0) :=
        externalInsertionMixedSplit_relativePerm_sign_eq_mixedInversionCount
          T externalTime σ htime

/-- The ambient time-order sign cancels the inter-sector crossing sign, leaving
precisely the local external-support reordering sign. This is the sign identity
consumed by the pointwise reassembled pairing and Dyson amplitudes. -/
theorem externalInsertionMixedSplit_global_sign_mul_mixedInversionSign_eq_local
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let localFixed := (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).symm
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let mixedSplit :=
      (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split
    StrictAnti (σ ∘ f) →
    Equiv.Perm.sign
        (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) *
      (-1 : ℤˣ) ^
        (∑ i : Fin (2 * (2 * T.card + E)),
          ∑ j : Fin (2 * (2 * S.card)),
            if mixedSplit (Sum.inr j) < mixedSplit (Sum.inl i) then 1 else 0) =
      Equiv.Perm.sign
        (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))) := by
  intro S order f localFixed split mixedSplit htime
  let localSign : ℤˣ :=
    Equiv.Perm.sign
      (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card)))))
  let globalSign : ℤˣ :=
    Equiv.Perm.sign
      (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ)
  let inversions : ℕ :=
    ∑ i : Fin (2 * (2 * T.card + E)),
      ∑ j : Fin (2 * (2 * S.card)),
        if mixedSplit (Sum.inr j) < mixedSplit (Sum.inl i) then 1 else 0
  have hsign : localSign * globalSign = (-1 : ℤˣ) ^ inversions :=
    externalInsertionMixedSplit_local_mul_global_sign_eq_mixedInversionCount
      T externalTime σ htime
  change globalSign * (-1 : ℤˣ) ^ inversions = localSign
  calc
    globalSign * (-1 : ℤˣ) ^ inversions =
        globalSign * (localSign * globalSign) := by rw [hsign]
    _ = localSign * (globalSign * globalSign) := by ac_rfl
    _ = localSign := by rw [Int.units_mul_self, mul_one]


end Common
end SecondQuantization
