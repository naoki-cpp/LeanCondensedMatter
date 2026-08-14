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
