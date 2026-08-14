import LeanCondensedMatter.Analysis.OrderedSimplex.StrictAntiCongr
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberExternalPiece
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberShuffleOrderedData

set_option linter.style.header false

/-!
# One canonical external-slot fiber as a binary shuffle integral

For a fixed `SlotShuffle m k`, the canonical fiber over its left-slot set is reindexed by a connected
order-`m` external diagram and order-`k` vacuum ordered data.  The previous files identify the
pointwise reassembled amplitude with the product of these local factors.  The coordinate lemmas from
`FiberShuffleCoordinates` then show that this product is exactly `SlotShuffle.integrand` on strictly
decreasing ambient times, which is sufficient under `orderedSimplexIntegral`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {i j : Mode}

/-- After standardizing a shuffle fiber, the ambient standalone external piece is heterogeneously
equal to the chosen order-`m` connected diagram. -/
theorem fixedExternalShuffleFiber_externalPiece_heq
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k)
    (ext : {d : FixedExternalTwoPointWickDiagram Mode m i j // d.1.IsExternallyConnected})
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k) :
    let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
    let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
    HEq d.1.externalPiece ext.1 := by
  classical
  let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
  let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
  have hp : fixedExternalShuffleFiberDataEquiv shuffle p = (ext, x) :=
    (fixedExternalShuffleFiberDataEquiv shuffle).apply_symm_apply (ext, x)
  have hext : connectedFixedExternalShuffleLeftEquiv shuffle p.1 = ext :=
    congrArg Prod.fst hp
  have hstd : HEq
      ((connectedFixedExternalTwoPointWickDiagramOnEquiv shuffle.leftSlots p.1).1) ext.1 := by
    have hval := congrArg Subtype.val hext
    simpa [connectedFixedExternalShuffleLeftEquiv] using hval
  exact (fixedExternalFiberEquiv_symm_externalPiece_heq shuffle.leftSlots p).trans hstd

/-- The inherited external-piece time coordinates of a shuffle fiber are its left shuffle
coordinates. -/
theorem fixedExternalShuffleFiber_externalPieceTimes_heq
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k)
    (ext : {d : FixedExternalTwoPointWickDiagram Mode m i j // d.1.IsExternallyConnected})
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k)
    (σ : Fin (m + k) → ℝ) :
    let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
    let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
    HEq (d.1.externalPieceTimes σ)
      (fun q : Fin m => σ (shuffle.slotEquiv (Sum.inl q))) := by
  classical
  let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
  let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
  have hd : d.1.1.externalInteractionPart = shuffle.leftSlots := d.2
  unfold FixedExternalTwoPointWickDiagram.externalPieceTimes
  rw [hd]
  simpa only [shuffle.card_leftSlots, Function.comp_apply] using
    (funext fun q : Fin m =>
      congrArg σ (slotShuffleLeftSlots_orderEmbOfFin shuffle q))

/-- The vacuum ordered datum recovered from the inverse standardized fiber is the chosen datum. -/
theorem fixedExternalShuffleFiber_vacuumOrderedData_heq
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k)
    (ext : {d : FixedExternalTwoPointWickDiagram Mode m i j // d.1.IsExternallyConnected})
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k) :
    let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
    HEq (Common.quarticDiagramEquivOrderedData
        (fixedExternalVacuumOrder shuffle.leftSlots) p.2) x := by
  classical
  let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
  have hp : fixedExternalShuffleFiberDataEquiv shuffle p = (ext, x) :=
    (fixedExternalShuffleFiberDataEquiv shuffle).apply_symm_apply (ext, x)
  have hvac := congrArg Prod.snd hp
  simpa [fixedExternalShuffleFiberDataEquiv,
    fixedExternalShuffleVacuumOrderedDataEquiv] using hvac

/-- The inherited vacuum times of a shuffle fiber are its right shuffle coordinates. -/
theorem fixedExternalShuffleFiber_vacuumTimes_heq
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k)
    (σ : Fin (m + k) → ℝ) :
    HEq (σ ∘ fixedExternalVacuumSlot shuffle.leftSlots)
      (fun q : Fin k => σ (shuffle.slotEquiv (Sum.inr q))) := by
  classical
  simpa only [slotShuffle_card_sdiff_leftSlots shuffle, Function.comp_apply] using
    (funext fun q : Fin k =>
      congrArg σ (fixedExternalVacuumSlot_leftSlots_eq_slotShuffleRight shuffle q))

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
  let p := (fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x)
  let d := (fixedExternalFiberEquiv shuffle.leftSlots).symm p
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
  have hvacAnti : StrictAnti (σ ∘ fixedExternalVacuumSlot shuffle.leftSlots) := by
    intro a b hab
    exact hσ (fixedExternalVacuumSlot_strictMono shuffle.leftSlots hab)
  have hprod :=
    fixedExternalOfSlotSplit_dysonFixedTimeAmplitude_eq_externalPiece_mul_orderedVacuumIntegrand
      ε β g shuffle.leftSlots p.1.1 p.1.2 p.2 τ τ' σ hvacAnti
  have hpiece := fixedExternalShuffleFiber_externalPiece_heq shuffle ext x
  have hleftTimes := fixedExternalShuffleFiber_externalPieceTimes_heq shuffle ext x σ
  have hvacData := fixedExternalShuffleFiber_vacuumOrderedData_heq shuffle ext x
  have hrightTimes := fixedExternalShuffleFiber_vacuumTimes_heq shuffle σ
  have hextValue :
      d.1.externalPiece.dysonFixedTimeAmplitude ε β g τ τ' (d.1.externalPieceTimes σ) =
        ext.1.dysonFixedTimeAmplitude ε β g τ τ'
          (fun q => σ (shuffle.slotEquiv (Sum.inl q))) := by
    cases hpiece
    cases hleftTimes
    rfl
  have hvacValue :
      orderedVacuumDysonIntegrand ε β g
          (Common.quarticDiagramEquivOrderedData
            (fixedExternalVacuumOrder shuffle.leftSlots) p.2)
          (σ ∘ fixedExternalVacuumSlot shuffle.leftSlots) =
        orderedVacuumDysonIntegrand ε β g x
          (fun q => σ (shuffle.slotEquiv (Sum.inr q))) := by
    cases hvacData
    cases hrightTimes
    rfl
  rw [show d.1 = fixedExternalOfSlotSplit shuffle.leftSlots p.1.1 p.2 by rfl]
  rw [hprod, hextValue, hvacValue]
  rfl

end Fermionic
end SecondQuantization
