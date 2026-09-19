import LeanCondensedMatter.Analysis.OrderedSimplex.StrictAntiCongr
import LeanCondensedMatter.Combinatorics.BinaryShuffleSlotEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumPairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Factorization.FiberDecomposition
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.FiberShuffleOrderedData

set_option linter.style.header false

/-!
# One canonical external-slot fiber as a binary shuffle integral

For a fixed `SlotShuffle m k`, the canonical fiber over its left-slot set is reindexed by a connected
order-`m` external diagram and order-`k` vacuum ordered data.  The previous files identify the
pointwise reassembled amplitude with the product of these local factors.  Generic binary-shuffle
coordinates then show that this product is exactly `SlotShuffle.integrand` on strictly decreasing
ambient times, which is sufficient under `orderedSimplexIntegral`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {i j : Mode}

private theorem cast_eq_of_heq {α β : Sort u} (hαβ : α = β) {a : α} {b : β}
    (hab : HEq a b) : cast hαβ a = b := by
  cases hαβ
  exact eq_of_heq hab

private theorem heq_finFun_of_cast {a b : ℕ} (h : a = b)
    (f : Fin a → ℝ) (g : Fin b → ℝ)
    (hfg : ∀ j : Fin b, f (Fin.cast h.symm j) = g j) : HEq f g := by
  cases h
  exact heq_of_eq (funext fun j => hfg j)

omit [LinearOrder Mode] [Fintype Mode] in
private theorem connectedFixedExternal_cast_val_heq {a b : ℕ} (h : a = b)
    (d : {d : FixedExternalTwoPointWickDiagram Mode a i j // d.1.IsExternallyConnected}) :
    HEq d.1
      ((Equiv.cast (by rw [h]) d :
        {d : FixedExternalTwoPointWickDiagram Mode b i j // d.1.IsExternallyConnected}).1) := by
  cases h
  rfl

private theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_cast
    {a b : ℕ} (h : a = b)
    (d : FixedExternalTwoPointWickDiagram Mode a i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin a → ℝ) :
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      (cast (by rw [h]) d : FixedExternalTwoPointWickDiagram Mode b i j).dysonFixedTimeAmplitude
        ε β g τ τ' (cast (by rw [h]) σ : Fin b → ℝ) := by
  cases h
  rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- After standardizing a shuffle fiber, the ambient standalone external piece is heterogeneously
equal to the chosen order-`m` connected diagram. -/
private theorem fixedExternalShuffleFiber_externalPiece_heq
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k)
    (ext : {d : FixedExternalTwoPointWickDiagram Mode m i j // d.1.IsExternallyConnected})
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k) :
    let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
    let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
    HEq d.1.externalPiece ext.1 := by
  classical
  dsimp only
  let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
  let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
  change HEq d.1.externalPiece ext.1
  have hbase := fixedExternalFiberEquiv_symm_externalPiece_heq shuffle.leftSlots p
  have hp : fixedExternalShuffleFiberDataEquiv shuffle p = (ext, x) :=
    (fixedExternalShuffleFiberDataEquiv shuffle).apply_symm_apply (ext, x)
  have hext : connectedFixedExternalShuffleLeftEquiv shuffle p.1 = ext :=
    congrArg Prod.fst hp
  have hcastVal : HEq
      ((connectedFixedExternalTwoPointWickDiagramOnEquiv shuffle.leftSlots p.1).1)
      ((connectedFixedExternalShuffleLeftEquiv shuffle p.1).1) := by
    unfold connectedFixedExternalShuffleLeftEquiv
    exact connectedFixedExternal_cast_val_heq shuffle.card_leftSlots
      (connectedFixedExternalTwoPointWickDiagramOnEquiv shuffle.leftSlots p.1)
  exact hbase.trans (hcastVal.trans (heq_of_eq (congrArg Subtype.val hext)))

omit [LinearOrder Mode] [Fintype Mode] in
/-- The inherited external-piece time coordinates of a shuffle fiber are its left shuffle
coordinates. -/
private theorem fixedExternalShuffleFiber_externalPieceTimes_heq
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k)
    (ext : {d : FixedExternalTwoPointWickDiagram Mode m i j // d.1.IsExternallyConnected})
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k)
    (σ : Fin (m + k) → ℝ) :
    let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
    let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
    HEq (d.1.1.externalPieceTimes σ)
      (fun q : Fin m => σ (shuffle.slotEquiv (Sum.inl q))) := by
  classical
  dsimp only
  let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
  let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
  change HEq (d.1.1.externalPieceTimes σ)
    (fun q : Fin m => σ (shuffle.slotEquiv (Sum.inl q)))
  have hsize : d.1.1.externalInteractionPart.card = m :=
    (congrArg Finset.card d.2).trans shuffle.card_leftSlots
  have horder := Finset.orderEmbOfFin_unique
    (s := d.1.1.externalInteractionPart) (h := hsize)
    (f := fun q : Fin m => shuffle.slotEquiv (Sum.inl q))
    (fun q => by
      rw [d.2]
      exact (shuffle.mem_leftSlots_iff _).2 ⟨q, rfl⟩)
    shuffle.strictMonoLeft
  apply heq_finFun_of_cast hsize
  intro q
  change σ (d.1.1.externalInteractionPart.orderEmbOfFin rfl (Fin.cast hsize.symm q)) = _
  apply congrArg σ
  convert congrFun horder.symm q using 1
  apply Fin.ext
  rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- The vacuum ordered datum recovered from the inverse standardized fiber is the chosen datum. -/
private theorem fixedExternalShuffleFiber_vacuumOrderedData_eq
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k)
    (ext : {d : FixedExternalTwoPointWickDiagram Mode m i j // d.1.IsExternallyConnected})
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k) :
    let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
    Common.quarticDiagramEquivOrderedData shuffle.rightSlotOrderEquiv p.2 = x := by
  dsimp only
  let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
  have hp : fixedExternalShuffleFiberDataEquiv shuffle p = (ext, x) :=
    (fixedExternalShuffleFiberDataEquiv shuffle).apply_symm_apply (ext, x)
  exact congrArg Prod.snd hp

private theorem orderedVacuumDysonIntegrand_orderIsoOfFin
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N k : ℕ} (S : Finset (Fin N)) (h : S.card = k)
    (vac : QuarticWickDiagram Mode N S) (σ : Fin N → ℝ) :
    orderedVacuumDysonIntegrand ε β g
        (Common.quarticDiagramEquivOrderedData
          (S.orderIsoOfFin rfl).toEquiv vac)
        (fun q => σ (((S.orderIsoOfFin rfl).toEquiv q).1)) =
      orderedVacuumDysonIntegrand ε β g
        (Common.quarticDiagramEquivOrderedData
          (S.orderIsoOfFin h).toEquiv vac)
        (fun q => σ (((S.orderIsoOfFin h).toEquiv q).1)) := by
  cases h
  rfl

private theorem orderedVacuumDysonIntegrand_rightSlotOrder
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k)
    (vac : QuarticWickDiagram Mode (m + k)
      ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots))
    (σ : Fin (m + k) → ℝ) :
    orderedVacuumDysonIntegrand ε β g
        (Common.quarticDiagramEquivOrderedData
          (slotSplitVacuumOrder shuffle.leftSlots) vac)
        (σ ∘ slotSplitVacuumSlot shuffle.leftSlots) =
      orderedVacuumDysonIntegrand ε β g
        (Common.quarticDiagramEquivOrderedData shuffle.rightSlotOrderEquiv vac)
        (fun q => σ ((shuffle.rightSlotOrderEquiv q).1)) := by
  change
    orderedVacuumDysonIntegrand ε β g
        (Common.quarticDiagramEquivOrderedData
          ((((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderIsoOfFin
            rfl).toEquiv) vac)
        (fun q => σ (((((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderIsoOfFin
          rfl).toEquiv q).1)) =
      orderedVacuumDysonIntegrand ε β g
        (Common.quarticDiagramEquivOrderedData
          ((((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderIsoOfFin
            shuffle.card_sdiff_leftSlots).toEquiv) vac)
        (fun q => σ (((((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderIsoOfFin
          shuffle.card_sdiff_leftSlots).toEquiv q).1))
  exact orderedVacuumDysonIntegrand_orderIsoOfFin ε β g
    ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots)
    shuffle.card_sdiff_leftSlots vac σ

/-- **One fixed shuffle fiber is exactly the corresponding binary shuffled product integral.** -/
theorem fixedExternalShuffleFiber_dysonAmplitude_eq_orderedSimplexIntegral
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ)
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k)
    (ext : {d : FixedExternalTwoPointWickDiagram Mode m i j // d.1.IsExternallyConnected})
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k) :
    let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
    let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
    d.1.dysonAmplitude ε β g τ τ' =
      intervalIntegral.orderedSimplexIntegral (m + k) β
        (shuffle.integrand
          (fun σ => ext.1.dysonFixedTimeAmplitude ε β g τ τ' σ)
          (orderedVacuumDysonIntegrand ε β g x)) := by
  classical
  dsimp only
  let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
  let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
  change d.1.dysonAmplitude ε β g τ τ' = _
  have hamp : d.1.dysonAmplitude ε β g τ τ' =
      intervalIntegral.orderedSimplexIntegral (m + k) β
        (fun σ => d.1.dysonFixedTimeAmplitude ε β g τ τ' σ) := by
    simp [FixedExternalTwoPointWickDiagram.dysonAmplitude,
      FixedExternalTwoPointWickDiagram.orderedSimplexContribution,
      FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude,
      intervalIntegral.orderedSimplexIntegral_smul]
  rw [hamp]
  apply intervalIntegral.orderedSimplexIntegral_congr_of_strictAnti (m + k) β hβ
  intro σ hσ _
  have hvacAnti : StrictAnti (σ ∘ slotSplitVacuumSlot shuffle.leftSlots) := by
    intro a b hab
    exact hσ (slotSplitVacuumSlot_strictMono shuffle.leftSlots hab)
  have hprod :=
    slotSplitDysonFixedTimeAmplitude_eq_external_mul_orderedVacuum
      ε β g shuffle.leftSlots p.1.1 p.1.2 p.2 τ τ' σ hvacAnti
  have hd : d.1 = fixedExternalOfSlotSplit shuffle.leftSlots p.1.1 p.2 := by
    rfl
  have hprod' : d.1.dysonFixedTimeAmplitude ε β g τ τ' σ =
      d.1.externalPiece.dysonFixedTimeAmplitude ε β g τ τ' (d.1.1.externalPieceTimes σ) *
        orderedVacuumDysonIntegrand ε β g
          (Common.quarticDiagramEquivOrderedData
            (slotSplitVacuumOrder shuffle.leftSlots) p.2)
          (σ ∘ slotSplitVacuumSlot shuffle.leftSlots) := by
    rw [hd]
    exact hprod
  have hpiece := fixedExternalShuffleFiber_externalPiece_heq shuffle ext x
  have hleftTimes := fixedExternalShuffleFiber_externalPieceTimes_heq shuffle ext x σ
  have hsize : d.1.1.externalInteractionPart.card = m :=
    (congrArg Finset.card d.2).trans shuffle.card_leftSlots
  have hpieceType :
      FixedExternalTwoPointWickDiagram Mode d.1.1.externalInteractionPart.card i j =
        FixedExternalTwoPointWickDiagram Mode m i j := by
    rw [hsize]
  have htimeType : (Fin d.1.1.externalInteractionPart.card → ℝ) = (Fin m → ℝ) := by
    rw [hsize]
  have hpieceEq : cast hpieceType d.1.externalPiece = ext.1 :=
    cast_eq_of_heq hpieceType hpiece
  have hleftTimesEq : cast htimeType (d.1.1.externalPieceTimes σ) =
      (fun q : Fin m => σ (shuffle.slotEquiv (Sum.inl q))) :=
    cast_eq_of_heq htimeType hleftTimes
  have hextValue :
      d.1.externalPiece.dysonFixedTimeAmplitude ε β g τ τ' (d.1.1.externalPieceTimes σ) =
        ext.1.dysonFixedTimeAmplitude ε β g τ τ'
          (fun q => σ (shuffle.slotEquiv (Sum.inl q))) := by
    have htransport := d.1.externalPiece.dysonFixedTimeAmplitude_cast
      hsize ε β g τ τ' (d.1.1.externalPieceTimes σ)
    simpa only [hpieceEq, hleftTimesEq] using htransport
  have hvacData :
      Common.quarticDiagramEquivOrderedData shuffle.rightSlotOrderEquiv p.2 = x := by
    simpa [p] using fixedExternalShuffleFiber_vacuumOrderedData_eq shuffle ext x
  have hvacTransport :=
    orderedVacuumDysonIntegrand_rightSlotOrder ε β g shuffle p.2 σ
  have hrightTimes :
      (fun q : Fin k => σ ((shuffle.rightSlotOrderEquiv q).1)) =
        (fun q : Fin k => σ (shuffle.slotEquiv (Sum.inr q))) := by
    funext q
    rw [shuffle.rightSlotOrderEquiv_val]
  have hvacValue :
      orderedVacuumDysonIntegrand ε β g
          (Common.quarticDiagramEquivOrderedData
            (slotSplitVacuumOrder shuffle.leftSlots) p.2)
          (σ ∘ slotSplitVacuumSlot shuffle.leftSlots) =
        orderedVacuumDysonIntegrand ε β g x
          (fun q => σ (shuffle.slotEquiv (Sum.inr q))) := by
    rw [hvacData, hrightTimes] at hvacTransport
    exact hvacTransport
  rw [hprod', hextValue, hvacValue]
  rfl

end Fermionic
end SecondQuantization
