import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberShuffleIntegral

set_option linter.style.header false

/-!
# Fixed-cardinality external-slot fibers as a Cauchy factor

At total perturbation order `m + k`, first restrict the canonical external-slot fibers to those whose
external component owns exactly `m` slots.  Reindex those slot sets by `SlotShuffle m k`, reindex each
fiber by its standardized connected external diagram and vacuum ordered data, and then apply the
binary shuffle product theorem.  The two remaining independent finite sums are exactly the connected
two-point coefficient at order `m` and the normalized vacuum coefficient at order `k`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {i j : Mode}

open Classical in
/-- A sum over the subtype of externally connected fixed-external diagrams is the connected
coefficient. -/
theorem sum_connectedFixedExternalTwoPointWickDiagram_dysonAmplitude_eq_connectedCoefficient
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (m : ℕ) :
    (∑ d : {d : FixedExternalTwoPointWickDiagram Mode m i j // d.1.IsExternallyConnected},
      d.1.dysonAmplitude ε β g τ τ') =
      connectedTwoPointDysonCoefficient ε β g i j τ τ' m := by
  unfold connectedTwoPointDysonCoefficient
  rw [Finset.sum_subtype
    (p := fun d : FixedExternalTwoPointWickDiagram Mode m i j => d.1.IsExternallyConnected)
    _ (fun x => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun d => d.dysonAmplitude ε β g τ τ')]

/-- **All fibers with external order `m` and vacuum order `k` sum to one Cauchy-product term.** -/
theorem sum_leftSlotSet_fixedExternalFiber_dysonAmplitude_eq_connected_mul_normalizedVacuum
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ)
    (m k : ℕ) :
    (∑ T : BinaryShuffle.LeftSlotSet m k,
      ∑ p : {ext : FixedExternalTwoPointWickDiagramOn Mode (m + k) T.1 i j //
              ext.1.IsExternallyConnected} ×
            QuarticWickDiagram Mode (m + k)
              ((Finset.univ : Finset (Fin (m + k))) \ T.1),
        ((fixedExternalFiberEquiv T.1).symm p).1.dysonAmplitude ε β g τ τ') =
      connectedTwoPointDysonCoefficient ε β g i j τ τ' m *
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
  classical
  rw [BinaryShuffle.sum_leftSlotSet]
  change
    (∑ shuffle : BinaryShuffle.SlotShuffle m k,
      ∑ p : {ext : FixedExternalTwoPointWickDiagramOn Mode (m + k) shuffle.leftSlots i j //
              ext.1.IsExternallyConnected} ×
            QuarticWickDiagram Mode (m + k)
              ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots),
        ((fixedExternalFiberEquiv shuffle.leftSlots).symm p).1.dysonAmplitude ε β g τ τ') = _
  calc
    (∑ shuffle : BinaryShuffle.SlotShuffle m k,
      ∑ p : {ext : FixedExternalTwoPointWickDiagramOn Mode (m + k) shuffle.leftSlots i j //
              ext.1.IsExternallyConnected} ×
            QuarticWickDiagram Mode (m + k)
              ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots),
        ((fixedExternalFiberEquiv shuffle.leftSlots).symm p).1.dysonAmplitude ε β g τ τ') =
      ∑ shuffle : BinaryShuffle.SlotShuffle m k,
        ∑ q : {ext : FixedExternalTwoPointWickDiagram Mode m i j //
                ext.1.IsExternallyConnected} ×
              Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
          ((fixedExternalFiberEquiv shuffle.leftSlots).symm
            ((fixedExternalShuffleFiberDataEquiv shuffle).symm q)).1.dysonAmplitude
              ε β g τ τ' := by
        apply Finset.sum_congr rfl
        intro shuffle _
        exact (Equiv.sum_comp (fixedExternalShuffleFiberDataEquiv shuffle).symm
          (fun p => ((fixedExternalFiberEquiv shuffle.leftSlots).symm p).1.dysonAmplitude
            ε β g τ τ')).symm
    _ = ∑ shuffle : BinaryShuffle.SlotShuffle m k,
        ∑ ext : {ext : FixedExternalTwoPointWickDiagram Mode m i j //
            ext.1.IsExternallyConnected},
          ∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
            ((fixedExternalFiberEquiv shuffle.leftSlots).symm
              ((fixedExternalShuffleFiberDataEquiv shuffle).symm (ext, x))).1.dysonAmplitude
                ε β g τ τ' := by
      apply Finset.sum_congr rfl
      intro shuffle _
      exact Fintype.sum_prod_type _
    _ = ∑ shuffle : BinaryShuffle.SlotShuffle m k,
        ∑ ext : {ext : FixedExternalTwoPointWickDiagram Mode m i j //
            ext.1.IsExternallyConnected},
          ∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
            intervalIntegral.orderedSimplexIntegral (m + k) β
              (shuffle.integrand
                (fun σ => ext.1.dysonFixedTimeAmplitude ε β g τ τ' σ)
                (orderedVacuumDysonIntegrand ε β g x)) := by
      apply Finset.sum_congr rfl
      intro shuffle _
      apply Finset.sum_congr rfl
      intro ext _
      apply Finset.sum_congr rfl
      intro x _
      exact fixedExternalShuffleFiber_dysonAmplitude_eq_orderedSimplexIntegral
        ε β hβ g τ τ' shuffle ext x
    _ = ∑ ext : {ext : FixedExternalTwoPointWickDiagram Mode m i j //
            ext.1.IsExternallyConnected},
        ∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
          ∑ shuffle : BinaryShuffle.SlotShuffle m k,
            intervalIntegral.orderedSimplexIntegral (m + k) β
              (shuffle.integrand
                (fun σ => ext.1.dysonFixedTimeAmplitude ε β g τ τ' σ)
                (orderedVacuumDysonIntegrand ε β g x)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ext _
      rw [Finset.sum_comm]
    _ = ∑ ext : {ext : FixedExternalTwoPointWickDiagram Mode m i j //
            ext.1.IsExternallyConnected},
        ∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
          ext.1.dysonAmplitude ε β g τ τ' *
            ((-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
              intervalIntegral.orderedSimplexIntegral k β
                (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)) := by
      apply Finset.sum_congr rfl
      intro ext _
      apply Finset.sum_congr rfl
      intro x _
      exact sum_slotShuffle_externalDyson_mul_orderedVacuumIntegrand_eq_mul
        ε β g τ τ' ext.1 x
    _ = (∑ ext : {ext : FixedExternalTwoPointWickDiagram Mode m i j //
              ext.1.IsExternallyConnected},
            ext.1.dysonAmplitude ε β g τ τ') *
          (∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
            (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
              intervalIntegral.orderedSimplexIntegral k β
                (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)) := by
      calc
        (∑ ext : {ext : FixedExternalTwoPointWickDiagram Mode m i j //
                ext.1.IsExternallyConnected},
          ∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
            ext.1.dysonAmplitude ε β g τ τ' *
              ((-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
                intervalIntegral.orderedSimplexIntegral k β
                  (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2))) =
            ∑ ext : {ext : FixedExternalTwoPointWickDiagram Mode m i j //
                ext.1.IsExternallyConnected},
              ext.1.dysonAmplitude ε β g τ τ' *
                (∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
                  (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
                    intervalIntegral.orderedSimplexIntegral k β
                      (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)) := by
              apply Finset.sum_congr rfl
              intro ext _
              exact (Finset.mul_sum _ _ _).symm
        _ = _ := (Finset.sum_mul _ _ _).symm
    _ = connectedTwoPointDysonCoefficient ε β g i j τ τ' m *
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
      rw [sum_connectedFixedExternalTwoPointWickDiagram_dysonAmplitude_eq_connectedCoefficient,
        sum_orderedVacuumDysonContribution_eq_normalizedDysonPartitionCoeff]

end Fermionic
end SecondQuantization
