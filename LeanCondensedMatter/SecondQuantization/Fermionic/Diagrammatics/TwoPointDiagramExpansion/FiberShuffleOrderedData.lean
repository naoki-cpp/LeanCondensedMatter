import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberShuffleProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberShuffleCoordinates
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
      {ext : FixedExternalTwoPointWickDiagram Mode m i j // ext.1.IsExternallyConnected} := by
  simpa only [shuffle.card_leftSlots] using
    (connectedFixedExternalTwoPointWickDiagramOnEquiv
      (Mode := Mode) (i := i) (j := j) shuffle.leftSlots)

/-- Read the vacuum half of a shuffle fiber in its inherited increasing order.  The resulting
ordered data has order `k`, independently of which ambient slots the shuffle assigns to it. -/
noncomputable def fixedExternalShuffleVacuumOrderedDataEquiv {m k : ℕ}
    (shuffle : BinaryShuffle.SlotShuffle m k) :
    QuarticWickDiagram Mode (m + k)
        ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots) ≃
      Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k := by
  simpa only [slotShuffle_card_sdiff_leftSlots shuffle] using
    (Common.quarticDiagramEquivOrderedData (fixedExternalVacuumOrder shuffle.leftSlots))

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
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T)) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      d.externalPiece.dysonFixedTimeAmplitude ε β g τ τ' (d.externalPieceTimes σ) *
        orderedVacuumDysonIntegrand ε β g
          (Common.quarticDiagramEquivOrderedData (fixedExternalVacuumOrder T) vac)
          (σ ∘ fixedExternalVacuumSlot T) := by
  rw [fixedExternalOfSlotSplit_dysonFixedTimeAmplitude_eq_externalPiece_mul_quarticIntegrand
    ε β g T ext hext vac τ τ' σ hσ]
  unfold orderedVacuumDysonIntegrand
  rw [couplingWeight_eq_prod_vertexLabel_order,
    vac.contractionIntegrand_eq_pairingEvaluation ε β (fixedExternalVacuumOrder T)]

/-- Summing the fixed-order Dyson contribution over ordered vacuum data gives the normalized vacuum
Dyson coefficient.  This is #1110 after removing the irrelevant ambient vertex set. -/
theorem sum_orderedVacuumDysonContribution_eq_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (k : ℕ) :
    (∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
      (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
        intervalIntegral.orderedSimplexIntegral k β
          (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)) =
      normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
  classical
  let S : Finset (Fin k) := Finset.univ
  let order : Common.QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
  let F : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card → ℂ :=
    fun x => (-1 : ℂ) ^ S.card * (∏ q : Fin S.card, g (x.1 q)) *
      intervalIntegral.orderedSimplexIntegral S.card β
        (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)
  calc
    (∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
      (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
        intervalIntegral.orderedSimplexIntegral k β
          (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)) =
        ∑ d : QuarticWickDiagram Mode k S,
          F (Common.quarticDiagramEquivOrderedData order d) := by
            simpa [S, F] using
              (Common.sum_quarticDiagram_eq_sum_orderedData order F).symm
    _ = ∑ d : QuarticWickDiagram Mode k S,
        (-1 : ℂ) ^ S.card * d.couplingWeight g *
          d.orderedSimplexContribution ε β order := by
      apply Finset.sum_congr rfl
      intro d _
      rw [couplingWeight_eq_prod_vertexLabel_order,
        orderedSimplexContribution_eq_pairingEvaluation]
      rfl
    _ = normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
      simpa [S] using
        (sum_quarticWickDiagram_fixedOrderDysonContribution_eq_normalizedDysonPartitionCoeff
          ε β g order)

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
  classical
  let S : Finset (Fin k) := Finset.univ
  let order : Common.QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
  let vac : QuarticWickDiagram Mode k S :=
    (Common.quarticDiagramEquivOrderedData order).symm x
  have hx : Common.quarticDiagramEquivOrderedData order vac = x :=
    (Common.quarticDiagramEquivOrderedData order).apply_symm_apply x
  have hlabels : (fun q => vac.vertexLabel (order q)) = x.1 := congrArg Prod.fst hx
  have hpair : vac.pairingInOrder order = x.2 := congrArg Prod.snd hx
  have hcoupling : vac.couplingWeight g = ∏ q : Fin k, g (x.1 q) := by
    rw [couplingWeight_eq_prod_vertexLabel_order]
    simpa [S] using congrArg (fun labels => ∏ q, g (labels q)) hlabels
  have hcontract : ∀ σ : Fin k → ℝ,
      vac.contractionIntegrand ε β order σ =
        flatVertexLegPairingEvaluation ε β x.1 σ x.2 := by
    intro σ
    rw [vac.contractionIntegrand_eq_pairingEvaluation ε β order]
    simpa [S] using congrArg
      (fun p : (Fin S.card → QuarticVertexLabel Mode) × Combinatorics.Pairing (2 * S.card) =>
        flatVertexLegPairingEvaluation ε β p.1 σ p.2) hx
  have hcontrib : vac.orderedSimplexContribution ε β order =
      intervalIntegral.orderedSimplexIntegral k β
        (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2) := by
    rw [orderedSimplexContribution_eq_pairingEvaluation]
    simpa [S, hlabels, hpair]
  have h := sum_slotShuffle_externalDyson_mul_quarticIntegrand_eq_mul
    ε β g τ τ' ext vac order
  simpa [S, orderedVacuumDysonIntegrand, hcoupling, hcontract, hcontrib] using h

end Fermionic
end SecondQuantization
