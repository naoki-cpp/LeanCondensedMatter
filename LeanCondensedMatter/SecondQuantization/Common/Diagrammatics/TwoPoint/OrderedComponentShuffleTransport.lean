import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.OrderedComponentTransport

set_option linter.style.header false

/-!
# Two-point component shuffles under interaction ordering

The graph isomorphism induced by an interaction-vertex order transports both the component index and
the number of interaction vertices in every component.  Reindexing the generic finite family shuffle
along this component equivalence therefore identifies the component-shuffle types before and after
ordering.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- Explicit transport of family shuffles along pointwise equal block sizes.  Unlike a raw
`Equiv.cast`, this keeps the local and ambient `Fin.cast`s visible to simplification. -/
noncomputable def familySlotShuffleCastSizeEquiv
    {ι : Type*} [Fintype ι] {size₁ size₂ : ι → ℕ}
    (h : ∀ i, size₁ i = size₂ i) :
    FamilySlotShuffle size₁ ≃ FamilySlotShuffle size₂ := by
  let hsum : (∑ i, size₁ i) = ∑ i, size₂ i := by
    apply Fintype.sum_congr
    intro i
    exact h i
  let localEquiv : (Σ i, Fin (size₂ i)) ≃ (Σ i, Fin (size₁ i)) :=
    Equiv.sigmaCongrRight fun i => finCongr (h i).symm
  exact
    { toFun := fun shuffle =>
        { slotEquiv := localEquiv.trans (shuffle.slotEquiv.trans (finCongr hsum))
          strictMono := by
            intro i a b hab
            change Fin.cast hsum (shuffle.slotEquiv (localEquiv ⟨i, a⟩)) <
              Fin.cast hsum (shuffle.slotEquiv (localEquiv ⟨i, b⟩))
            simpa [localEquiv] using
              (Fin.castOrderIso hsum).strictMono
                (shuffle.strictMono i
                  ((Fin.castOrderIso (h i).symm).strictMono hab)) }
      invFun := fun shuffle =>
        { slotEquiv := localEquiv.symm.trans (shuffle.slotEquiv.trans (finCongr hsum.symm))
          strictMono := by
            intro i a b hab
            have ha : localEquiv.symm ⟨i, a⟩ = ⟨i, Fin.cast (h i) a⟩ := by
              apply localEquiv.injective
              simp [localEquiv]
            have hb : localEquiv.symm ⟨i, b⟩ = ⟨i, Fin.cast (h i) b⟩ := by
              apply localEquiv.injective
              simp [localEquiv]
            change Fin.cast hsum.symm (shuffle.slotEquiv (localEquiv.symm ⟨i, a⟩)) <
              Fin.cast hsum.symm (shuffle.slotEquiv (localEquiv.symm ⟨i, b⟩))
            rw [ha, hb]
            exact (Fin.castOrderIso hsum.symm).strictMono
              (shuffle.strictMono i ((Fin.castOrderIso (h i)).strictMono hab)) }
      left_inv := by
        intro shuffle
        apply FamilySlotShuffle.ext
        apply Equiv.ext
        intro x
        change Fin.cast hsum.symm
            (Fin.cast hsum
              (shuffle.slotEquiv (localEquiv (localEquiv.symm x)))) =
          shuffle.slotEquiv x
        rw [localEquiv.apply_symm_apply]
        simp
      right_inv := by
        intro shuffle
        apply FamilySlotShuffle.ext
        apply Equiv.ext
        intro x
        change Fin.cast hsum
            (Fin.cast hsum.symm
              (shuffle.slotEquiv (localEquiv.symm (localEquiv x)))) =
          shuffle.slotEquiv x
        rw [localEquiv.symm_apply_apply]
        simp }

/-- Component interaction shuffles of an explicit ordered diagram are canonically the component
interaction shuffles of the original ambient diagram. -/
def TwoPointDiagram.inInteractionOrderComponentShuffleEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) :
    (d.inInteractionOrder order).ComponentInteractionShuffle ≃
      d.ComponentInteractionShuffle := by
  let dOrdered := d.inInteractionOrder order
  let ePart := d.inInteractionOrderComponentPartEquiv order
  let hfamily : FamilySlotShuffle dOrdered.interactionComponentSize ≃
      FamilySlotShuffle (fun B => d.interactionComponentSize (ePart B)) :=
    familySlotShuffleCastSizeEquiv fun B =>
      d.interactionComponentSize_inInteractionOrder_eq order B
  exact dOrdered.componentInteractionFamilyShuffleEquiv.symm |>.trans <|
    hfamily.trans <|
      (FamilySlotShuffle.reindexEquiv ePart d.interactionComponentSize).symm |>.trans
        d.componentInteractionFamilyShuffleEquiv

/-- Evaluation of component-shuffle transport on a component/local slot from the ordered diagram. -/
@[simp]
theorem TwoPointDiagram.inInteractionOrderComponentShuffleEquiv_slotEquiv_apply
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S)
    (shuffle : (d.inInteractionOrder order).ComponentInteractionShuffle)
    (B : (d.inInteractionOrder order).componentPartition.parts)
    (i : Fin ((d.inInteractionOrder order).interactionComponentSize B)) :
    (d.inInteractionOrderComponentShuffleEquiv order shuffle).slotEquiv
        ⟨d.inInteractionOrderComponentPartEquiv order B,
          Fin.cast (d.interactionComponentSize_inInteractionOrder_eq order B) i⟩ =
      Fin.cast (by simp) (shuffle.slotEquiv ⟨B, i⟩) := by
  simp [TwoPointDiagram.inInteractionOrderComponentShuffleEquiv,
    familySlotShuffleCastSizeEquiv,
    TwoPointDiagram.componentInteractionFamilyShuffleEquiv,
    FamilySlotShuffle.reindexEquiv, FamilySlotShuffleTo.castTotalEquiv]

end

end Common
end SecondQuantization
