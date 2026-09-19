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

private theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_externalPieceOfCardEq
    {n m : ℕ} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (h : d.1.externalInteractionPart.card = m)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.externalPiece.dysonFixedTimeAmplitude ε β g τ τ' (d.1.externalPieceTimes σ) =
      (d.externalPieceOfCardEq h).dysonFixedTimeAmplitude ε β g τ τ'
        (d.1.externalPieceTimesOfCardEq h σ) := by
  cases h
  rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- After standardizing a shuffle fiber at its known left-slot count, the standalone external piece
is exactly the chosen order-`m` connected diagram. -/
private theorem fixedExternalShuffleFiber_externalPieceOfCardEq_eq
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k)
    (ext : {d : FixedExternalTwoPointWickDiagram Mode m i j // d.1.IsExternallyConnected})
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k) :
    let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
    let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
    let hsize : d.1.1.externalInteractionPart.card = m :=
      (congrArg Finset.card d.2).trans shuffle.card_leftSlots
    d.1.externalPieceOfCardEq hsize = ext.1 := by
  dsimp only
  let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
  let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
  let hsize : d.1.1.externalInteractionPart.card = m :=
    (congrArg Finset.card d.2).trans shuffle.card_leftSlots
  have hbase := fixedExternalFiberEquiv_symm_externalPieceOfCardEq_eq
    shuffle.leftSlots shuffle.card_leftSlots p
  have hp : fixedExternalShuffleFiberDataEquiv shuffle p = (ext, x) :=
    (fixedExternalShuffleFiberDataEquiv shuffle).apply_symm_apply (ext, x)
  have hext : connectedFixedExternalShuffleLeftEquiv shuffle p.1 = ext :=
    congrArg Prod.fst hp
  have hbase' :
      d.1.externalPieceOfCardEq hsize =
        (connectedFixedExternalShuffleLeftEquiv shuffle p.1).1 := by
    simpa [d, hsize, connectedFixedExternalShuffleLeftEquiv] using hbase
  exact hbase'.trans (congrArg Subtype.val hext)

omit [LinearOrder Mode] [Fintype Mode] in
/-- The inherited external-piece times at the known left-slot count are the left shuffle
coordinates. -/
private theorem fixedExternalShuffleFiber_externalPieceTimesOfCardEq_eq
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k)
    (ext : {d : FixedExternalTwoPointWickDiagram Mode m i j // d.1.IsExternallyConnected})
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k)
    (σ : Fin (m + k) → ℝ) :
    let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
    let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
    let hsize : d.1.1.externalInteractionPart.card = m :=
      (congrArg Finset.card d.2).trans shuffle.card_leftSlots
    d.1.1.externalPieceTimesOfCardEq hsize σ =
      (fun q : Fin m => σ (shuffle.slotEquiv (Sum.inl q))) := by
  classical
  dsimp only
  let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
  let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
  let hsize : d.1.1.externalInteractionPart.card = m :=
    (congrArg Finset.card d.2).trans shuffle.card_leftSlots
  change (fun q : Fin m =>
    σ (d.1.1.externalInteractionPart.orderEmbOfFin hsize q)) = _
  have horder := Finset.orderEmbOfFin_unique
    (s := d.1.1.externalInteractionPart) (h := hsize)
    (f := fun q : Fin m => shuffle.slotEquiv (Sum.inl q))
    (fun q => by
      rw [d.2]
      exact (shuffle.mem_leftSlots_iff _).2 ⟨q, rfl⟩)
    shuffle.strictMonoLeft
  funext q
  apply congrArg σ
  convert congrFun horder.symm q using 1
omit [LinearOrder Mode] [Fintype Mode] in
/-- The vacuum ordered datum recovered from the inverse standardized fiber is the chosen datum. -/
private theorem fixedExternalShuffleFiber_vacuumOrderedData_eq
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k)
    (ext : {d : FixedExternalTwoPointWickDiagram Mode m i j // d.1.IsExternallyConnected})
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k) :
    let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
    Common.quarticDiagramEquivOrderedData shuffle.sdiffLeftSlotsOrderEquiv p.2 = x := by
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

private theorem orderedVacuumDysonIntegrand_sdiffLeftSlotsOrder
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
        (Common.quarticDiagramEquivOrderedData shuffle.sdiffLeftSlotsOrderEquiv vac)
        (fun q => σ ((shuffle.sdiffLeftSlotsOrderEquiv q).1)) := by
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
  have hsize : d.1.1.externalInteractionPart.card = m :=
    (congrArg Finset.card d.2).trans shuffle.card_leftSlots
  have hpieceEq : d.1.externalPieceOfCardEq hsize = ext.1 := by
    simpa [p, d, hsize] using
      fixedExternalShuffleFiber_externalPieceOfCardEq_eq shuffle ext x
  have hleftTimesEq : d.1.1.externalPieceTimesOfCardEq hsize σ =
      (fun q : Fin m => σ (shuffle.slotEquiv (Sum.inl q))) := by
    simpa [p, d, hsize] using
      fixedExternalShuffleFiber_externalPieceTimesOfCardEq_eq shuffle ext x σ
  have hextTransport :=
    d.1.dysonFixedTimeAmplitude_externalPieceOfCardEq hsize ε β g τ τ' σ
  have hextValue :
      d.1.externalPiece.dysonFixedTimeAmplitude ε β g τ τ' (d.1.1.externalPieceTimes σ) =
        ext.1.dysonFixedTimeAmplitude ε β g τ τ'
          (fun q => σ (shuffle.slotEquiv (Sum.inl q))) := by
    rw [hpieceEq, hleftTimesEq] at hextTransport
    exact hextTransport
  have hvacData :
      Common.quarticDiagramEquivOrderedData shuffle.sdiffLeftSlotsOrderEquiv p.2 = x := by
    simpa [p] using fixedExternalShuffleFiber_vacuumOrderedData_eq shuffle ext x
  have hvacTransport :=
    orderedVacuumDysonIntegrand_sdiffLeftSlotsOrder ε β g shuffle p.2 σ
  have hrightTimes :
      (fun q : Fin k => σ ((shuffle.sdiffLeftSlotsOrderEquiv q).1)) =
        (fun q : Fin k => σ (shuffle.slotEquiv (Sum.inr q))) := by
    funext q
    rw [shuffle.sdiffLeftSlotsOrderEquiv_val]
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
