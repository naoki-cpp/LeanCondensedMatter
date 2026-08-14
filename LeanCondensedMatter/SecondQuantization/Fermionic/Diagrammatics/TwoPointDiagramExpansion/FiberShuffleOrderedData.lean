import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberShuffleProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotShuffleCoordinates
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing

set_option linter.style.header false

/-!
# Ordered-data coordinates for the vacuum factor in the fiber shuffle

The external-slot fiber changes its ambient complement as the slot shuffle changes.  The quartic
vacuum diagram itself therefore cannot be held fixed across the shuffle sum.  Its ordered data can:
for the inherited increasing order, a vacuum diagram is exactly a slot-indexed label sequence and a
pairing.

This file exposes the fixed-order vacuum integrand in those order-only coordinates and transports the
binary ordered-simplex product theorem to that representation.  It is the representation bridge
needed before reindexing the fixed-cardinality external-slot fibers into one Cauchy-product sum.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {i j : Mode}

/-- The fixed-order quartic contraction integrand depends on a diagram only through its ordered
vertex labels and its pairing transported to that same order. -/
theorem QuarticWickDiagram.contractionIntegrand_eq_pairingEvaluation
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (ε : Mode → ℝ) (β : ℝ) (order : Common.QuarticVertexOrder S)
    (τ : Fin S.card → ℝ) :
    d.contractionIntegrand ε β order τ =
      flatVertexLegPairingEvaluation ε β
        (fun q => d.vertexLabel (order q)) τ (d.pairingInOrder order) := by
  simp only [QuarticWickDiagram.contractionIntegrand, flatVertexLegPairingEvaluation,
    Combinatorics.Pairing.evaluation, flatVertexLegPairValue]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun pr _ => ?_)
  rw [orderedQuarticPairValue_eq_freeGibbsDensityOperator_expectation,
    orderedQuarticLegOperator]

/-- The Dyson-signed vacuum integrand written only in fixed ordered quartic data. -/
noncomputable def orderedVacuumDysonIntegrand
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) {k : ℕ}
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k)
    (σ : Fin k → ℝ) : ℂ :=
  (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
    flatVertexLegPairingEvaluation ε β x.1 σ x.2

/-- Standardize the connected external half of a shuffle fiber onto `Fin m`. -/
noncomputable def connectedFixedExternalShuffleLeftEquiv {m k : ℕ}
    (shuffle : BinaryShuffle.SlotShuffle m k) :
    {ext : FixedExternalTwoPointWickDiagramOn Mode (m + k) shuffle.leftSlots i j //
        ext.1.IsExternallyConnected} ≃
      {ext : FixedExternalTwoPointWickDiagram Mode m i j // ext.1.IsExternallyConnected} :=
  (connectedFixedExternalTwoPointWickDiagramOnEquiv
      (Mode := Mode) (i := i) (j := j) shuffle.leftSlots).trans
    (Equiv.cast (by rw [shuffle.card_leftSlots]))

/-- Read the vacuum half of a shuffle fiber in its inherited increasing order.  The resulting
ordered data has order `k`, independently of which ambient slots the shuffle assigns to it. -/
noncomputable def fixedExternalShuffleVacuumOrderedDataEquiv {m k : ℕ}
    (shuffle : BinaryShuffle.SlotShuffle m k) :
    QuarticWickDiagram Mode (m + k)
        ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots) ≃
      Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k :=
  (Common.quarticDiagramEquivOrderedData (slotSplitVacuumOrder shuffle.leftSlots)).trans
    (Equiv.cast (by rw [slotShuffle_card_sdiff_leftSlots shuffle]))

/-- A fixed-cardinality fiber has shuffle-independent local data: one connected order-`m` external
diagram and one order-`k` vacuum label/pairing datum. -/
noncomputable def fixedExternalShuffleFiberDataEquiv {m k : ℕ}
    (shuffle : BinaryShuffle.SlotShuffle m k) :
    ({ext : FixedExternalTwoPointWickDiagramOn Mode (m + k) shuffle.leftSlots i j //
        ext.1.IsExternallyConnected} ×
      QuarticWickDiagram Mode (m + k)
        ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots)) ≃
      ({ext : FixedExternalTwoPointWickDiagram Mode m i j // ext.1.IsExternallyConnected} ×
        Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k) :=
  Equiv.prodCongr (connectedFixedExternalShuffleLeftEquiv shuffle)
    (fixedExternalShuffleVacuumOrderedDataEquiv shuffle)

/-- The canonical fixed-fiber pointwise product can be written with the vacuum factor entirely in
ordered-data coordinates. -/
theorem fixedExternalOfSlotSplit_dysonFixedTimeAmplitude_eq_externalPiece_mul_orderedVacuumIntegrand
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {n : ℕ} (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (hext : ext.1.IsExternallyConnected)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      d.externalPiece.dysonFixedTimeAmplitude ε β g τ τ' (d.1.externalPieceTimes σ) *
        orderedVacuumDysonIntegrand ε β g
          (Common.quarticDiagramEquivOrderedData (slotSplitVacuumOrder T) vac)
          (σ ∘ slotSplitVacuumSlot T) := by
  dsimp only
  rw [fixedExternalOfSlotSplit_dysonFixedTimeAmplitude_eq_externalPiece_mul_quarticIntegrand
    ε β g T ext hext vac τ τ' σ hσ]
  unfold orderedVacuumDysonIntegrand
  rw [couplingWeight_eq_prod_vertexLabel_order vac g (slotSplitVacuumOrder T),
    vac.contractionIntegrand_eq_pairingEvaluation ε β (slotSplitVacuumOrder T)]
  rfl

/-- Summing the fixed-order Dyson contribution over ordered vacuum data gives the normalized vacuum
Dyson coefficient.  This is the fixed-order vacuum theorem with the irrelevant ambient vertex set
removed entirely. -/
theorem sum_orderedVacuumDysonContribution_eq_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (k : ℕ) :
    (∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
      (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
        intervalIntegral.orderedSimplexIntegral k β
          (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)) =
      normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
  classical
  have hkey :=
    dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairingEvaluation
      ε β g (Finset.univ : Finset (Fin k))
  rw [Finset.card_univ, Fintype.card_fin] at hkey
  calc
    (∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
      (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
        intervalIntegral.orderedSimplexIntegral k β
          (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)) =
        (-1 : ℂ) ^ k *
          ∑ q : Fin k → QuarticVertexLabel Mode,
            (∏ i, g (q i)) *
              ∑ pairing : Combinatorics.Pairing (2 * k),
                intervalIntegral.orderedSimplexIntegral k β
                  (fun σ => flatVertexLegPairingEvaluation ε β q σ pairing) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum, Finset.mul_sum]
      simp only [mul_assoc]
    _ = normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
      have hfac : ((k.factorial : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero k
      apply mul_left_cancel₀ hfac
      simpa [dysonVertexMoment, mul_assoc] using hkey.symm

/-- The binary shuffle product theorem in ordered-data coordinates for the vacuum factor.

Unlike a quartic diagram on an ambient complement, `x` is independent of the ambient locations of
those complement slots.  This is the form that can be held fixed while summing the external-slot
shuffles. -/
theorem sum_slotShuffle_externalDyson_mul_orderedVacuumIntegrand_eq_mul
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) {m k : ℕ}
    (ext : FixedExternalTwoPointWickDiagram Mode m i j)
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k) :
    (∑ shuffle : BinaryShuffle.SlotShuffle m k,
      intervalIntegral.orderedSimplexIntegral (m + k) β
        (shuffle.integrand
          (fun σ => ext.dysonFixedTimeAmplitude ε β g τ τ' σ)
          (orderedVacuumDysonIntegrand ε β g x))) =
      ext.dysonAmplitude ε β g τ τ' *
        ((-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
          intervalIntegral.orderedSimplexIntegral k β
            (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)) := by
  have hext :
      intervalIntegral.MeasurableLocallyBounded
        (fun σ : Fin m → ℝ => ext.dysonFixedTimeAmplitude ε β g τ τ' σ) :=
    ext.measurableLocallyBounded_dysonFixedTimeAmplitude ε β g τ τ'
  have hvac :
      intervalIntegral.MeasurableLocallyBounded
        (orderedVacuumDysonIntegrand ε β g x) :=
    (intervalIntegral.measurableLocallyBounded_const
      ((-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)))).mul
      (intervalIntegral.Continuous.measurableLocallyBounded
        (continuous_flatVertexLegPairingEvaluation ε β x.1 x.2))
  have hextIntegral :
      intervalIntegral.orderedSimplexIntegral m β
        (fun σ => ext.dysonFixedTimeAmplitude ε β g τ τ' σ) =
        ext.dysonAmplitude ε β g τ τ' := by
    simp [FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude,
      FixedExternalTwoPointWickDiagram.dysonAmplitude,
      FixedExternalTwoPointWickDiagram.orderedSimplexContribution,
      intervalIntegral.orderedSimplexIntegral_smul]
  have hvacIntegral :
      intervalIntegral.orderedSimplexIntegral k β
        (orderedVacuumDysonIntegrand ε β g x) =
        (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
          intervalIntegral.orderedSimplexIntegral k β
            (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2) := by
    unfold orderedVacuumDysonIntegrand
    exact intervalIntegral.orderedSimplexIntegral_smul k β
      ((-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)))
      (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)
  have h :=
    BinaryShuffle.sum_slotShuffle_orderedSimplexIntegral_integrand_eq_mul_of_measurableLocallyBounded
      m k β
      (fun σ => ext.dysonFixedTimeAmplitude ε β g τ τ' σ)
      (orderedVacuumDysonIntegrand ε β g x) hext hvac
  rw [hextIntegral, hvacIntegral] at h
  exact h

end Fermionic
end SecondQuantization
