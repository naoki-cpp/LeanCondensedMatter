import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffle
import LeanCondensedMatter.Combinatorics.FinpartitionOrderShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.ComponentFactorization
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.DysonExpansion.Pairing

set_option linter.style.header false

/-!
# Bosonic Dyson amplitude factorization over connected components

The component-local vertex orders and global shuffles are handled by the generic
finite-partition order decomposition. The ordered-simplex family-shuffle identity factors
time integrals, and the existing bosonic pairing factorization handles thermal contractions.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

variable {Mode : Type*} [Finite Mode]

omit [Finite Mode] in
/-- The scalar quartic imaginary-time factor of an assembled global order is the family-shuffle
integrand of the corresponding component-local time factors. -/
private theorem QuarticDiagram.quarticVertexSequenceTimeFactor_assembleVertexOrder
    (ε : Mode → ℝ) {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) :
    Common.quarticVertexSequenceTimeFactor ε
        (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i)) τ =
      shuffle.ambientIntegrand
        (fun B : d.vertexGraph.componentPartitionOn.parts =>
          Common.quarticVertexSequenceTimeFactor ε
            (fun i => (d.restrictComponent B.2).vertexLabel (orders B i))) τ := by
  classical
  unfold Common.quarticVertexSequenceTimeFactor Combinatorics.FamilySlotShuffleTo.ambientIntegrand
  rw [← Equiv.prod_comp shuffle.slotEquiv]
  rw [Finset.prod_sigma']
  apply Fintype.prod_congr
  intro x
  obtain ⟨B, i⟩ := x
  simp only [Combinatorics.FamilySlotShuffleTo.timeAssignment_apply]
  rw [← d.restrictComponent_vertexLabel_componentOrder orders shuffle B i]

omit [Finite Mode] in
/-- For fixed component-local vertex orders, summing the physical ordered Dyson amplitude over all
order-preserving component shuffles gives the product of the corresponding component-local ordered
Dyson amplitudes. -/
private theorem QuarticDiagram.sum_shuffle_orderedDysonThermalAmplitude_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S)
    (orders : d.ComponentVertexOrders) (t : ℝ) :
    (∑ shuffle : d.ComponentShuffle,
      QuarticDiagram.orderedDysonThermalAmplitude ε β g d
        (d.assembleVertexOrder orders shuffle) t) =
      ∏ B : d.vertexGraph.componentPartitionOn.parts,
        QuarticDiagram.orderedDysonThermalAmplitude ε β g
          (d.restrictComponent B.2) (orders B) t := by
  classical
  let localIntegrand :
      ∀ B : d.vertexGraph.componentPartitionOn.parts,
        (Fin (B : Finset (Fin N)).card → ℝ) → ℂ :=
    fun B => Common.quarticVertexSequenceTimeFactor ε
      (fun i => (d.restrictComponent B.2).vertexLabel (orders B i))
  have hcard :
      (∑ B : d.vertexGraph.componentPartitionOn.parts, (B : Finset (Fin N)).card) = S.card := by
    rw [Finset.sum_coe_sort]
    exact d.vertexGraph.componentPartitionOn.sum_card_parts
  have htime :
      (∑ shuffle : d.ComponentShuffle,
        intervalIntegral.orderedSimplexIntegral S.card t
          (Common.quarticVertexSequenceTimeFactor ε
            (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i)))) =
        ∏ B : d.vertexGraph.componentPartitionOn.parts,
          intervalIntegral.orderedSimplexIntegral (B : Finset (Fin N)).card t
            (localIntegrand B) := by
    rw [show
      (fun shuffle : d.ComponentShuffle =>
        intervalIntegral.orderedSimplexIntegral S.card t
          (Common.quarticVertexSequenceTimeFactor ε
            (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i)))) =
        (fun shuffle : d.ComponentShuffle =>
          intervalIntegral.orderedSimplexIntegral S.card t
            (shuffle.ambientIntegrand localIntegrand)) by
      funext shuffle
      congr 1
      funext τ
      exact QuarticDiagram.quarticVertexSequenceTimeFactor_assembleVertexOrder
        ε d orders shuffle τ]
    exact Combinatorics.FamilySlotShuffleTo.sum_integral_eq_prod
      (fun B : d.vertexGraph.componentPartitionOn.parts => (B : Finset (Fin N)).card)
      S.card hcard t localIntegrand
      (fun B => intervalIntegral.Continuous.measurableLocallyBounded
        (Common.continuous_quarticVertexSequenceTimeFactor ε
          (fun i => (d.restrictComponent B.2).vertexLabel (orders B i))))
  simp only [QuarticDiagram.orderedDysonThermalAmplitude, Common.quarticDysonSequenceCoeff]
  have hpair (shuffle : d.ComponentShuffle) :
      QuarticDiagram.orderedThermalPairingValue ε β d
          (d.assembleVertexOrder orders shuffle) =
        ∏ B : d.vertexGraph.componentPartitionOn.parts,
          QuarticDiagram.orderedThermalPairingValue ε β
            (d.restrictComponent B.2) (orders B) :=
    QuarticDiagram.orderedThermalPairingValue_eq_prod_components ε β d orders shuffle
  simp_rw [hpair]
  have hvertex (shuffle : d.ComponentShuffle) :
      (∏ i, g (d.vertexLabel (d.assembleVertexOrder orders shuffle i))) = d.vertexWeight g := by
    unfold Common.QuarticDiagram.vertexWeight
    exact Equiv.prod_comp (d.assembleVertexOrder orders shuffle) (fun v => g (d.vertexLabel v))
  simp_rw [hvertex]
  let pairingProduct : ℂ :=
    ∏ B : d.vertexGraph.componentPartitionOn.parts,
      QuarticDiagram.orderedThermalPairingValue ε β
        (d.restrictComponent B.2) (orders B)
  rw [show
      (∑ shuffle : d.ComponentShuffle,
        (-1 : ℂ) ^ S.card * d.vertexWeight g *
            intervalIntegral.orderedSimplexIntegral S.card t
              (Common.quarticVertexSequenceTimeFactor ε
                (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i))) *
          pairingProduct) =
        ((-1 : ℂ) ^ S.card * d.vertexWeight g) *
          ((∑ shuffle : d.ComponentShuffle,
            intervalIntegral.orderedSimplexIntegral S.card t
              (Common.quarticVertexSequenceTimeFactor ε
                (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i)))) *
            pairingProduct) by
      calc
        _ = ∑ shuffle : d.ComponentShuffle,
            ((-1 : ℂ) ^ S.card * d.vertexWeight g) *
              (intervalIntegral.orderedSimplexIntegral S.card t
                (Common.quarticVertexSequenceTimeFactor ε
                  (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i))) *
                pairingProduct) := by
              apply Finset.sum_congr rfl
              intro shuffle _
              ring
        _ = ((-1 : ℂ) ^ S.card * d.vertexWeight g) *
            ∑ shuffle : d.ComponentShuffle,
              (intervalIntegral.orderedSimplexIntegral S.card t
                (Common.quarticVertexSequenceTimeFactor ε
                  (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i))) *
                pairingProduct) := by
              rw [Finset.mul_sum]
        _ = _ := by
              rw [Finset.sum_mul]]
  rw [htime]
  rw [Common.QuarticDiagram.dysonSign_mul_vertexWeight_eq_prod_components d g]
  dsimp only [pairingProduct, localIntegrand]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro B _
  change
    ((-1 : ℂ) ^ (B : Finset (Fin N)).card *
        (d.restrictComponent B.2).vertexWeight g) *
        (_ * _) =
      (((-1 : ℂ) ^ (B : Finset (Fin N)).card *
        ∏ x, g ((d.restrictComponent B.2).vertexLabel (orders B x))) * _) * _
  rw [Common.QuarticDiagram.vertexWeight_eq_prod_vertexLabel_order
    (d.restrictComponent B.2) g (orders B)]
  ring

omit [Finite Mode] in
/-- The physical bosonic quartic Dyson diagram amplitude factors over the connected components of
the diagram. The proof reindexes global vertex orders into component-local orders and shuffles, then
uses the finite-family ordered-simplex shuffle identity for the time integrals. -/
theorem QuarticDiagram.dysonThermalAmplitude_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S) (t : ℝ) :
    QuarticDiagram.dysonThermalAmplitude ε β g d t =
      ∏ B : d.vertexGraph.componentPartitionOn.parts,
        QuarticDiagram.dysonThermalAmplitude ε β g (d.restrictComponent B.2) t := by
  classical
  unfold QuarticDiagram.dysonThermalAmplitude
  simpa only [one_mul] using
    (Finpartition.sum_order_eq_mul_prod_sum_partOrders
      d.vertexGraph.componentPartitionOn
      (fun order : Common.QuarticVertexOrder S =>
        QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t)
      (fun B order =>
        QuarticDiagram.orderedDysonThermalAmplitude ε β g
          (d.restrictComponent B.2) order t)
      (1 : ℂ) (fun orders => by
        change (∑ shuffle : d.ComponentShuffle,
          QuarticDiagram.orderedDysonThermalAmplitude ε β g d
            (d.assembleVertexOrder orders shuffle) t) =
          (1 : ℂ) * ∏ B : d.vertexGraph.componentPartitionOn.parts,
            QuarticDiagram.orderedDysonThermalAmplitude ε β g
              (d.restrictComponent B.2) (orders B) t
        simpa only [one_mul] using
          QuarticDiagram.sum_shuffle_orderedDysonThermalAmplitude_eq_prod_components
            ε β g d orders t))

end
end Bosonic
end SecondQuantization
