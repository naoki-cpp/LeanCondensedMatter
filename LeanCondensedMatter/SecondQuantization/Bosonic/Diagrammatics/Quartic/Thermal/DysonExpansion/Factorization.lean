import LeanCondensedMatter.Analysis.OrderedSimplex.PartitionOrderIntegral
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.ComponentFactorization
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.DysonExpansion.Pairing

set_option linter.style.header false

/-!
# Bosonic Dyson amplitude factorization over connected components

The component-local vertex orders and global shuffles are handled by the generic
finite-partition order decomposition. The ordered-simplex family-shuffle identity factors
the complete integrands, including Dyson signs, vertex weights, and static thermal pairing values.
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

/-- Complete fixed-order integrand, with the time-independent Dyson prefactor and
thermal pairing value included in the scalar multiplying the time factor. -/
private noncomputable def QuarticDiagram.dysonThermalIntegrand
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S)
    (order : Common.QuarticVertexOrder S) (τ : Fin S.card → ℝ) : ℂ :=
  ((-1 : ℂ) ^ S.card * d.vertexWeight g *
    QuarticDiagram.orderedThermalPairingValue ε β d order) *
      Common.quarticVertexSequenceTimeFactor ε (fun i => d.vertexLabel (order i)) τ

omit [Finite Mode] in
private theorem QuarticDiagram.orderedDysonThermalAmplitude_eq_integral
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S)
    (order : Common.QuarticVertexOrder S) (t : ℝ) :
    QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t =
      intervalIntegral.orderedSimplexIntegral S.card t
        (QuarticDiagram.dysonThermalIntegrand ε β g d order) := by
  unfold QuarticDiagram.orderedDysonThermalAmplitude Common.quarticDysonSequenceCoeff
    QuarticDiagram.dysonThermalIntegrand
  rw [intervalIntegral.orderedSimplexIntegral_smul,
    Common.QuarticDiagram.vertexWeight_eq_prod_vertexLabel_order d g order]
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
  simp_rw [QuarticDiagram.orderedDysonThermalAmplitude_eq_integral]
  exact Finpartition.sum_order_orderedSimplexIntegral_eq_prod_sum_partOrders
    d.vertexGraph.componentPartitionOn t
    (fun order => QuarticDiagram.dysonThermalIntegrand ε β g d order)
    (fun B order => QuarticDiagram.dysonThermalIntegrand ε β g
      (d.restrictComponent B.2) order)
    (fun orders shuffle => by
      funext τ
      dsimp only [QuarticDiagram.dysonThermalIntegrand]
      rw [Common.QuarticDiagram.dysonSign_mul_vertexWeight_eq_prod_components d g,
        QuarticDiagram.orderedThermalPairingValue_eq_prod_components ε β d orders shuffle,
        QuarticDiagram.quarticVertexSequenceTimeFactor_assembleVertexOrder ε d orders shuffle τ]
      simp only [FamilySlotShuffleTo.ambientIntegrand, QuarticDiagram.dysonThermalIntegrand,
        Common.QuarticDiagram.restrictComponentConnected, Finset.prod_mul_distrib])
    (fun B order => intervalIntegral.Continuous.measurableLocallyBounded
      (continuous_const.mul
        (Common.continuous_quarticVertexSequenceTimeFactor ε
          (fun i => (d.restrictComponent B.2).vertexLabel (order i)))))

end
end Bosonic
end SecondQuantization
