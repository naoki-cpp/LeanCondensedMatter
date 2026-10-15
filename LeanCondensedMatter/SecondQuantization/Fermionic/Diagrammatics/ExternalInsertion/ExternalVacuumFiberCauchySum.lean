import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.FixedExternalFiberSum
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalVacuumFiberShuffleIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalVacuumShuffleIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.FiberShuffleOrderedData

set_option linter.style.header false

/-!
# Fixed-cardinality arbitrary-external support fibers

At interaction order m + k, fixing the size of the externally supported slots
and summing the corresponding fibers gives the order-m vacuum-free
arbitrary-external Dyson coefficient times the order-k normalized vacuum
coefficient. The constraint on the external labels belongs only to the
external-support factor; different externally supported components need not
be connected.
-/

namespace SecondQuantization
namespace Fermionic

open Common
open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Reordering the two subtype predicates retains precisely the fixed-label
vacuum-free diagrams. -/
private def vacuumFreeFixedExternalSubtypeEquiv {E m : ℕ}
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode) :
    {d : {d : ExternalInsertionWickDiagram Mode E m //
      HasNoVacuumComponent d.vertexGraph} // d.1.externalLabel = externalLabel} ≃
      VacuumFreeFixedExternalInsertionWickDiagram Mode E m externalLabel where
  toFun d := ⟨⟨d.1.1, d.2⟩, d.1.2⟩
  invFun d := ⟨⟨d.1.1, d.2⟩, d.1.2⟩
  left_inv d := by
    rcases d with ⟨⟨d, hd⟩, hl⟩
    rfl
  right_inv d := by
    rcases d with ⟨⟨d, hl⟩, hd⟩
    rfl

open Classical in
private theorem vacuumFreeExternalInsertionDysonCoefficient_eq_sum_if
    {E m : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) :
    vacuumFreeExternalInsertionDysonCoefficient ε β g externalLabel externalTime m =
      ∑ ext : {d : ExternalInsertionWickDiagram Mode E m //
        HasNoVacuumComponent d.vertexGraph},
        if ext.1.externalLabel = externalLabel then
          ext.1.dysonAmplitude ε β g externalTime else 0 := by
  classical
  unfold vacuumFreeExternalInsertionDysonCoefficient
  let X := {d : ExternalInsertionWickDiagram Mode E m //
    HasNoVacuumComponent d.vertexGraph}
  let e := vacuumFreeFixedExternalSubtypeEquiv (Mode := Mode) (m := m) externalLabel
  calc
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode E m externalLabel,
      d.1.1.dysonAmplitude ε β g externalTime) =
        ∑ d : {d : X // d.1.externalLabel = externalLabel},
          d.1.1.dysonAmplitude ε β g externalTime := by
        exact (Equiv.sum_comp e (fun d : VacuumFreeFixedExternalInsertionWickDiagram
          Mode E m externalLabel => d.1.1.dysonAmplitude ε β g externalTime)).symm
    _ = ∑ ext : X,
          if ext.1.externalLabel = externalLabel then
            ext.1.dysonAmplitude ε β g externalTime else 0 := by
      calc
        _ = ∑ ext ∈ (Finset.univ : Finset X).filter
              (fun ext => ext.1.externalLabel = externalLabel),
              ext.1.dysonAmplitude ε β g externalTime := by
            rw [Finset.sum_subtype
              (p := fun ext : X => ext.1.externalLabel = externalLabel)
              (Finset.univ : Finset X)
              (fun _ => by simp)
              (fun ext : X => ext.1.dysonAmplitude ε β g externalTime)]
        _ = _ := by
          simp only [Finset.sum_filter]

omit [LinearOrder Mode] [Fintype Mode] in
private theorem standardizedSupportFiber_externalLabel
    {E m k : ℕ} (shuffle : SlotShuffle m k)
    (q : {d : ExternalInsertionWickDiagram Mode E m //
        HasNoVacuumComponent d.vertexGraph} ×
      OrderedQuarticDiagramData (QuarticVertexLabel Mode) k) :
    let p := (ExternalInsertionDiagram.standardizedSupportFiberDataEquiv
      (E := E) shuffle).symm q
    let d := (ExternalInsertionDiagram.externalSupportFiberEquiv
      (Finset.subset_univ shuffle.leftSlots)).symm p
    d.1.externalLabel = q.1.1.externalLabel := rfl

open Classical in
/-- The sum over all fixed-cardinality external-support fibers is one factor
of the Cauchy convolution with the normalized vacuum Dyson series. -/
theorem externalInsertionFixedCardinalityFiberSum_eq_cauchyFactor
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (m k : ℕ) :
    (∑ T ∈ Finset.powersetCard m (Finset.univ : Finset (Fin (m + k))),
      ∑ p : {ext : ExternalInsertionDiagram
        (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) E (m + k) T //
        HasNoVacuumComponent ext.vertexGraph} ×
        QuarticDiagram (QuarticVertexLabel Mode) (m + k)
          ((Finset.univ : Finset (Fin (m + k))) \ T),
        if p.1.1.externalLabel = externalLabel then
          ExternalInsertionWickDiagram.dysonAmplitude
            (((ExternalInsertionDiagram.externalSupportFiberEquiv
              (Finset.subset_univ T)).symm p).1 :
                ExternalInsertionWickDiagram Mode E (m + k))
            ε β g externalTime
        else 0) =
      vacuumFreeExternalInsertionDysonCoefficient
          ε β g externalLabel externalTime m *
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
  classical
  rw [externalInsertionDysonCoefficient_powersetCard_eq_sum_standardizedSupportShuffle]
  let X := {d : ExternalInsertionWickDiagram Mode E m //
    HasNoVacuumComponent d.vertexGraph}
  let Y := OrderedQuarticDiagramData (QuarticVertexLabel Mode) k
  let vacuum : Y → ℂ := fun x =>
    (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
      intervalIntegral.orderedSimplexIntegral k β
        (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)
  let shuffled : SlotShuffle m k → X → Y → ℂ := fun shuffle ext x =>
    intervalIntegral.orderedSimplexIntegral (m + k) β
      (shuffle.integrand
        (fun σ => ext.1.dysonFixedTimeAmplitude ε β g externalTime σ)
        (fun σ => (-1 : ℂ) ^ k * (∏ i : Fin k, g (x.1 i)) *
          flatVertexLegPairingEvaluation ε β x.1 σ x.2))
  calc
    (∑ shuffle : SlotShuffle m k,
      ∑ q : X × Y,
        let d : ExternalInsertionWickDiagram Mode E (m + k) :=
          ((ExternalInsertionDiagram.externalSupportFiberEquiv
            (Finset.subset_univ shuffle.leftSlots)).symm
            ((ExternalInsertionDiagram.standardizedSupportFiberDataEquiv
              (E := E) shuffle).symm q)).1
        if d.externalLabel = externalLabel then
          d.dysonAmplitude ε β g externalTime else 0) =
        ∑ shuffle : SlotShuffle m k,
          ∑ ext : X, ∑ x : Y,
            if ext.1.externalLabel = externalLabel then
              shuffled shuffle ext x else 0 := by
      apply Finset.sum_congr rfl
      intro shuffle _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro ext _
      apply Finset.sum_congr rfl
      intro x _
      have hl := standardizedSupportFiber_externalLabel (Mode := Mode)
        shuffle (ext, x)
      dsimp only at hl
      dsimp only
      rw [hl]
      split_ifs with h
      · exact externalInsertionStandardizedSupportFiber_dysonAmplitude_eq_shuffleIntegral
          ε β hβ g shuffle (ext, x) externalTime
      · rfl
    _ = ∑ ext : X, ∑ x : Y,
          ∑ shuffle : SlotShuffle m k,
            if ext.1.externalLabel = externalLabel then
              shuffled shuffle ext x else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ext _
      rw [Finset.sum_comm]
    _ = ∑ ext : X, ∑ x : Y,
          if ext.1.externalLabel = externalLabel then
            ext.1.dysonAmplitude ε β g externalTime * vacuum x else 0 := by
      apply Finset.sum_congr rfl
      intro ext _
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : ext.1.externalLabel = externalLabel
      · simp only [h, ite_true]
        exact sum_slotShuffleExternalInsertionDysonIntegral_eq_mul_orderedVacuum
          ε β g externalTime ext.1 x
      · simp only [h, ite_false, Finset.sum_const_zero]
    _ = (∑ ext : X,
          if ext.1.externalLabel = externalLabel then
            ext.1.dysonAmplitude ε β g externalTime else 0) *
        (∑ x : Y, vacuum x) := by
      calc
        _ = ∑ ext : X, ∑ x : Y,
            (if ext.1.externalLabel = externalLabel then
              ext.1.dysonAmplitude ε β g externalTime else 0) * vacuum x := by
          apply Finset.sum_congr rfl
          intro ext _
          apply Finset.sum_congr rfl
          intro x _
          split_ifs <;> simp
        _ = ∑ ext : X,
            (if ext.1.externalLabel = externalLabel then
              ext.1.dysonAmplitude ε β g externalTime else 0) *
                (∑ x : Y, vacuum x) := by
          apply Finset.sum_congr rfl
          intro ext _
          exact (Finset.mul_sum _ _ _).symm
        _ = _ := (Finset.sum_mul _ _ _).symm
    _ = vacuumFreeExternalInsertionDysonCoefficient
          ε β g externalLabel externalTime m *
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
      rw [← vacuumFreeExternalInsertionDysonCoefficient_eq_sum_if,
        show (∑ x : Y, vacuum x) =
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) k from
            sum_orderedVacuumDysonContribution_eq_normalizedDysonPartitionCoeff
              ε β g k]

end Fermionic
end SecondQuantization
