import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticThermalAmplitude
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentEvaluation
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentVertexProduct

set_option linter.style.header false

/-!
# Connected-component factorization of bosonic thermal quartic amplitudes

The free thermal field attached to a component-local ordered leg agrees with the field attached to
its image in an assembled global order. Common's Statistics-generic pairing-evaluation theorem then
factors the bosonic thermal pairing value over connected components. Combining that result with the
Common scalar prefactor factorization gives coefficientwise factorization of the full ordered thermal
amplitude.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

variable {Mode : Type*} {N : ℕ}

/-- The ordered free thermal field family is local under the Common component ordered-leg
embedding. -/
theorem QuarticDiagram.orderedFreeThermalFieldFamily_componentOrderedLeg
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    d.orderedFreeThermalFieldFamily (d.assembleVertexOrder orders shuffle)
        (d.componentOrderedLeg shuffle B p) =
      QuarticDiagram.orderedFreeThermalFieldFamily (d.restrictComponent B.2) (orders B) p := by
  unfold QuarticDiagram.orderedFreeThermalFieldFamily quarticFreeThermalFieldFamily
  simp only [d.orderedQuarticLegEquiv_componentOrderedLeg]
  rw [d.restrictComponent_vertexLabel_componentOrder orders shuffle B]

variable [DecidableEq Mode]

/-- The free thermal pair kernel agrees between a component-local ordered pair and its image in an
assembled global order. -/
theorem QuarticDiagram.freeThermalPairValue_componentOrderedLeg
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts)
    (a b : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    freeThermalPairValue ε β
        (d.orderedFreeThermalFieldFamily (d.assembleVertexOrder orders shuffle)
          (d.componentOrderedLeg shuffle B a))
        (d.orderedFreeThermalFieldFamily (d.assembleVertexOrder orders shuffle)
          (d.componentOrderedLeg shuffle B b)) =
      freeThermalPairValue ε β
        (QuarticDiagram.orderedFreeThermalFieldFamily (d.restrictComponent B.2) (orders B) a)
        (QuarticDiagram.orderedFreeThermalFieldFamily (d.restrictComponent B.2) (orders B) b) := by
  rw [d.orderedFreeThermalFieldFamily_componentOrderedLeg orders shuffle B,
    d.orderedFreeThermalFieldFamily_componentOrderedLeg orders shuffle B]

/-- The bosonic thermal contraction value of an assembled pairing is the product of the thermal
contraction values of its connected-component restrictions. -/
theorem QuarticDiagram.orderedThermalPairingValue_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :
    d.orderedThermalPairingValue ε β (d.assembleVertexOrder orders shuffle) =
      ∏ B : d.componentPartition.parts,
        QuarticDiagram.orderedThermalPairingValue ε β (d.restrictComponent B.2) (orders B) := by
  classical
  simpa only [QuarticDiagram.orderedThermalPairingValue] using
    d.pairingInOrder_evaluation_eq_prod_components Statistics.boson orders shuffle
      (fun a b => freeThermalPairValue ε β
        (d.orderedFreeThermalFieldFamily (d.assembleVertexOrder orders shuffle) a)
        (d.orderedFreeThermalFieldFamily (d.assembleVertexOrder orders shuffle) b))
      (fun B a b => freeThermalPairValue ε β
        (QuarticDiagram.orderedFreeThermalFieldFamily (d.restrictComponent B.2) (orders B) a)
        (QuarticDiagram.orderedFreeThermalFieldFamily (d.restrictComponent B.2) (orders B) b))
      (fun B a b => d.freeThermalPairValue_componentOrderedLeg ε β orders shuffle B a b)

/-- The coefficientwise bosonic ordered thermal amplitude factors over connected components. -/
theorem QuarticDiagram.orderedThermalAmplitude_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    d.orderedThermalAmplitude ε β g (d.assembleVertexOrder orders shuffle) =
      ∏ B : d.componentPartition.parts,
        QuarticDiagram.orderedThermalAmplitude ε β g (d.restrictComponent B.2) (orders B) := by
  classical
  unfold QuarticDiagram.orderedThermalAmplitude
  rw [Common.QuarticDiagram.dysonSign_mul_vertexWeight_eq_prod_restrictComponentConnected d g]
  simp only [Common.QuarticDiagram.restrictComponentConnected]
  rw [d.orderedThermalPairingValue_eq_prod_components ε β orders shuffle]
  rw [← Finset.prod_mul_distrib]

end
end Bosonic
end SecondQuantization
