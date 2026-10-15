import LeanCondensedMatter.Analysis.OrderedSimplex.BinarySlotShuffle
import LeanCondensedMatter.Combinatorics.SlotShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SupportStandardization
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.ExternalSupportFiber
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalVacuumIntegrated
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Pairing

set_option linter.style.header false

/-!
# Vacuum ordered data in binary support-slot shuffle coordinates

The vacuum factor inherited from a support-slot split has the same oriented
quartic pairing value and Dyson vertex weights as the fixed ordered vacuum
datum. The time coordinates are the right embedding of the binary shuffle.
This is the vacuum-coordinate part of the integrated external/vacuum fiber bridge.
-/

namespace SecondQuantization
namespace Fermionic

open Common
open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

private theorem quarticVacuumDysonFactor_orderIsoOfFin
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N k : ℕ} (S : Finset (Fin N)) (h : S.card = k)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) N S)
    (σ : Fin N → ℝ) :
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin N := fun i => (S.orderIsoOfFin rfl i).1
    let x : OrderedQuarticDiagramData (QuarticVertexLabel Mode) k :=
      quarticDiagramEquivOrderedData (S.orderIsoOfFin h).toEquiv vac
    ((-1 : ℂ) ^ S.card * vac.vertexWeight g) *
      (vac.pairingInOrder order).evaluation
        ((vac.pairingInOrder order).weight Statistics.fermion)
        (flatVertexLegPairValue ε β
          (fun i => vac.vertexLabel (S.orderIsoOfFin rfl i)) (σ ∘ f)) =
      ((-1 : ℂ) ^ k * (∏ i : Fin k, g (x.1 i))) *
        flatVertexLegPairingEvaluation ε β x.1
          (fun i => σ ((S.orderIsoOfFin h i).1)) x.2 := by
  cases h
  dsimp only
  rw [vac.vertexWeight_eq_prod_vertexLabel_order g (S.orderIsoOfFin rfl).toEquiv]
  rfl

/-- The vacuum Dyson factor of a split diagram is the ordered-quartic factor
evaluated on the right coordinates of the ambient binary slot shuffle.
In particular, no reversal of a fermionic pairing kernel is used. -/
theorem externalInsertionVacuumDysonFactor_eq_shuffleOrderedData
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {m k : ℕ} (shuffle : SlotShuffle m k)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) (m + k)
      ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots))
    (σ : Fin (m + k) → ℝ) :
    let S := (Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin (m + k) := fun i => (S.orderIsoOfFin rfl i).1
    let x : OrderedQuarticDiagramData (QuarticVertexLabel Mode) k :=
      quarticDiagramEquivOrderedData shuffle.sdiffLeftSlotsOrderEquiv vac
    ((-1 : ℂ) ^ S.card * vac.vertexWeight g) *
      (vac.pairingInOrder order).evaluation
        ((vac.pairingInOrder order).weight Statistics.fermion)
        (flatVertexLegPairValue ε β
          (fun i => vac.vertexLabel (S.orderIsoOfFin rfl i)) (σ ∘ f)) =
      ((-1 : ℂ) ^ k * (∏ i : Fin k, g (x.1 i))) *
        flatVertexLegPairingEvaluation ε β x.1
          (fun i => σ (shuffle.slotEquiv (Sum.inr i))) x.2 := by
  dsimp only
  have h := quarticVacuumDysonFactor_orderIsoOfFin ε β g
    ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots)
    shuffle.card_sdiff_leftSlots vac σ
  have htime :
      (fun i : Fin k =>
          σ (((((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderIsoOfFin
            shuffle.card_sdiff_leftSlots) i).1)) =
        (fun i : Fin k => σ (shuffle.slotEquiv (Sum.inr i))) := by
    funext i
    exact congrArg σ (shuffle.sdiffLeftSlots_orderEmbOfFin i)
  rw [htime] at h
  exact h


/-- Changing the chosen proof of the left-support cardinality does not change the
standalone Dyson amplitude or its inherited time coordinates. -/
private theorem externalSupportDysonFactor_orderIsoOfFin
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {E N m : ℕ} (T : Finset (Fin N)) (h : T.card = m)
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E N T)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin N → ℝ) :
    let e : ↥T ≃ ↥(Finset.univ : Finset (Fin T.card)) :=
      (T.orderIsoOfFin rfl).toEquiv.symm.trans
        (Equiv.subtypeUnivEquiv
          (fun i : Fin T.card => Finset.mem_univ i)).symm
    let e' : ↥T ≃ ↥(Finset.univ : Finset (Fin m)) :=
      (T.orderIsoOfFin h).toEquiv.symm.trans
        (Equiv.subtypeUnivEquiv
          (fun i : Fin m => Finset.mem_univ i)).symm
    ExternalInsertionWickDiagram.dysonFixedTimeAmplitude (ext.slotCongr e) ε β g externalTime
      (fun i => σ ((T.orderIsoOfFin rfl i).1)) =
      ExternalInsertionWickDiagram.dysonFixedTimeAmplitude (ext.slotCongr e') ε β g externalTime
        (fun i => σ ((T.orderIsoOfFin h i).1)) := by
  cases h
  rfl

/-- The standalone Dyson factor obtained from the supported interaction slots
uses precisely the left coordinates of a binary slot shuffle. -/
theorem externalInsertionSupportDysonFactor_eq_shuffleStandardizedData
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {E m k : ℕ} (shuffle : SlotShuffle m k)
    (ext : {d : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E (m + k) shuffle.leftSlots //
        HasNoVacuumComponent d.vertexGraph})
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin (m + k) → ℝ) :
    let T := shuffle.leftSlots
    let e : ↥T ≃ ↥(Finset.univ : Finset (Fin T.card)) :=
      (T.orderIsoOfFin rfl).toEquiv.symm.trans
        (Equiv.subtypeUnivEquiv
          (fun i : Fin T.card => Finset.mem_univ i)).symm
    let f : Fin T.card → Fin (m + k) :=
      fun i => (T.orderIsoOfFin rfl i).1
    ExternalInsertionWickDiagram.dysonFixedTimeAmplitude (ext.1.slotCongr e) ε β g externalTime (σ ∘ f) =
      ExternalInsertionWickDiagram.dysonFixedTimeAmplitude
      ((ExternalInsertionDiagram.standardizeVacuumFree
        T shuffle.card_leftSlots) ext).1 ε β g externalTime
          (fun i => σ (shuffle.slotEquiv (Sum.inl i))) := by
  dsimp only
  have h := externalSupportDysonFactor_orderIsoOfFin ε β g
    shuffle.leftSlots shuffle.card_leftSlots ext.1 externalTime σ
  have htime :
      (fun i : Fin m =>
        σ ((shuffle.leftSlots.orderIsoOfFin shuffle.card_leftSlots i).1)) =
      (fun i : Fin m => σ (shuffle.slotEquiv (Sum.inl i))) := by
    funext i
    exact congrArg σ (shuffle.leftSlots_orderEmbOfFin i)
  rw [htime] at h
  exact h

/-- A fixed standardized support fiber is the corresponding binary shuffle
integral, with the vacuum factor evaluated at correctly oriented pair endpoints.
This is the bridge from fixed-support integration to the shuffle sum. -/
theorem externalInsertionStandardizedSupportFiber_dysonAmplitude_eq_shuffleIntegral
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    {E m k : ℕ} (shuffle : SlotShuffle m k)
    (q : {ext : ExternalInsertionDiagram
          (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) E m
          (Finset.univ : Finset (Fin m)) //
          HasNoVacuumComponent ext.vertexGraph} ×
        OrderedQuarticDiagramData (QuarticVertexLabel Mode) k)
    (externalTime : Fin (2 * E) → ℝ) :
    let p := (ExternalInsertionDiagram.standardizedSupportFiberDataEquiv
      (E := E) shuffle).symm q
    let d := (ExternalInsertionDiagram.externalSupportFiberEquiv
      (Finset.subset_univ shuffle.leftSlots)).symm p
    ExternalInsertionWickDiagram.dysonAmplitude d.1 ε β g externalTime =
      intervalIntegral.orderedSimplexIntegral (m + k) β
        (shuffle.integrand
          (fun σ => ExternalInsertionWickDiagram.dysonFixedTimeAmplitude q.1.1 ε β g externalTime σ)
          (fun σ => (-1 : ℂ) ^ k * (∏ i : Fin k, g (q.2.1 i)) *
            flatVertexLegPairingEvaluation ε β q.2.1 σ q.2.2)) := by
  classical
  dsimp only
  let p := (ExternalInsertionDiagram.standardizedSupportFiberDataEquiv
    (E := E) shuffle).symm q
  let d := (ExternalInsertionDiagram.externalSupportFiberEquiv
    (Finset.subset_univ shuffle.leftSlots)).symm p
  have hd :
      d.1 = ExternalInsertionDiagram.ofSlotSplit
        (Finset.subset_univ shuffle.leftSlots) p.1.1 p.2 := rfl
  rw [hd]
  rw [externalInsertionOfSlotSplit_dysonAmplitude_eq_integral_standalone_mul_vacuum
    ε β hβ g shuffle.leftSlots p.1.1 p.2 externalTime]
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  have hext := externalInsertionSupportDysonFactor_eq_shuffleStandardizedData
    ε β g shuffle p.1 externalTime σ
  have hvac := externalInsertionVacuumDysonFactor_eq_shuffleOrderedData
    ε β g shuffle p.2 σ
  have hp :
      (ExternalInsertionDiagram.standardizedSupportFiberDataEquiv
        (E := E) shuffle) p = q :=
    (ExternalInsertionDiagram.standardizedSupportFiberDataEquiv
      (E := E) shuffle).apply_symm_apply q
  have hpExt :
      (ExternalInsertionDiagram.standardizeVacuumFree
        shuffle.leftSlots shuffle.card_leftSlots p.1) = q.1 :=
    congrArg Prod.fst hp
  have hpVac :
      quarticDiagramEquivOrderedData shuffle.sdiffLeftSlotsOrderEquiv p.2 = q.2 :=
    congrArg Prod.snd hp
  change
    ExternalInsertionWickDiagram.dysonFixedTimeAmplitude
      (p.1.1.slotCongr
        ((shuffle.leftSlots.orderIsoOfFin rfl).toEquiv.symm.trans
          (Equiv.subtypeUnivEquiv
            (fun i : Fin shuffle.leftSlots.card => Finset.mem_univ i)).symm))
      ε β g externalTime
      (σ ∘ fun i => (shuffle.leftSlots.orderIsoOfFin rfl i).1) *
    (((-1 : ℂ) ^
        ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).card *
        p.2.vertexWeight g) *
      (p.2.pairingInOrder
        ((((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderIsoOfFin
          rfl).toEquiv)).evaluation
          ((p.2.pairingInOrder
            ((((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderIsoOfFin
              rfl).toEquiv)).weight Statistics.fermion)
          (flatVertexLegPairValue ε β
            (fun i => p.2.vertexLabel
              (((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderIsoOfFin
                rfl i))
            (σ ∘ fun i =>
              (((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderIsoOfFin
                rfl i).1))) =
    ExternalInsertionWickDiagram.dysonFixedTimeAmplitude q.1.1 ε β g externalTime
      (fun i => σ (shuffle.slotEquiv (Sum.inl i))) *
    ((-1 : ℂ) ^ k * (∏ i : Fin k, g (q.2.1 i)) *
      flatVertexLegPairingEvaluation ε β q.2.1
        (fun i => σ (shuffle.slotEquiv (Sum.inr i))) q.2.2)
  rw [hext, hvac, hpExt, hpVac]

end Fermionic
end SecondQuantization
