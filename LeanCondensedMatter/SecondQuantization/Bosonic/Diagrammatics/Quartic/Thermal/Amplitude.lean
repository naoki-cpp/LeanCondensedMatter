import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.ThermalField
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ConcreteExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Concrete bosonic quartic diagram amplitudes

This module places the free-boson thermal pair kernel from the concrete thermal layer on the existing
ordered quartic-diagram structure.  A vertex order turns the diagram labels into a finite ordered
list, and `pairingInOrder` selects one perfect pairing of the resulting local thermal fields.  The
scalar diagram value is evaluated through `Combinatorics.Pairing.evaluation`.

The amplitude here is coefficientwise/algebraic.  It includes the quartic coupling product and Dyson
sign, but no ordered-simplex time integration and no completed-space boundedness claim.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

variable {Mode : Type*} {N : ℕ}

/-- File-local classical equality matches the concrete free-thermal kernel. -/
local instance instDecidableEqQuarticThermalAmplitude : DecidableEq Mode := Classical.decEq Mode

/-- The flattened free thermal fields of a bosonic quartic diagram in a chosen vertex order. -/
noncomputable def QuarticDiagram.orderedFreeThermalFieldFamily {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (Common.QuarticVertexLabel Mode) N S)
    (order : Common.QuarticVertexOrder S) :
    Fin (2 * (2 * S.card)) → FreeThermalField Mode :=
  quarticFreeThermalFieldFamily (fun i => d.vertexLabel (order i))

/-- The concrete free thermal contraction value of one ordered bosonic quartic diagram. -/
noncomputable def QuarticDiagram.orderedThermalPairingValue
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (Common.QuarticVertexLabel Mode) N S)
    (order : Common.QuarticVertexOrder S) : ℂ :=
  (d.pairingInOrder order).evaluation
    ((d.pairingInOrder order).weight .boson)
    (fun a b => freeThermalPairValue ε β
      (QuarticDiagram.orderedFreeThermalFieldFamily d order a)
      (QuarticDiagram.orderedFreeThermalFieldFamily d order b))

/-- The coefficientwise scalar amplitude of one ordered bosonic quartic diagram, including the
Dyson sign and quartic coupling product. -/
noncomputable def QuarticDiagram.orderedThermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (Common.QuarticVertexLabel Mode) N S)
    (order : Common.QuarticVertexOrder S) : ℂ :=
  (-1 : ℂ) ^ S.card * d.vertexWeight g *
    QuarticDiagram.orderedThermalPairingValue ε β d order

/-- The full Wick pairing sum for the ordered vertex labels underlying a quartic diagram. -/
noncomputable def QuarticDiagram.orderedThermalWickSum
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (Common.QuarticVertexLabel Mode) N S)
    (order : Common.QuarticVertexOrder S) : ℂ :=
  ∑ pairing : Pairing (2 * S.card),
    pairing.evaluation (pairing.weight .boson)
      (fun a b => freeThermalPairValue ε β
        (QuarticDiagram.orderedFreeThermalFieldFamily d order a)
        (QuarticDiagram.orderedFreeThermalFieldFamily d order b))

variable [Fintype Mode]

/-- The concrete Gibbs expectation of the ordered quartic local-leg product is exactly the sum over
the pairing amplitudes carried by the existing quartic diagram combinatorics. -/
theorem QuarticDiagram.freeGibbsExpectation_eq_orderedThermalWickSum
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (Common.QuarticVertexLabel Mode) N S)
    (order : Common.QuarticVertexOrder S) :
    freeGibbsExpectation ε β
        (quarticFreeThermalOrderedProduct (fun i => d.vertexLabel (order i))) =
      QuarticDiagram.orderedThermalWickSum ε β d order := by
  have hwick := freeGibbsExpectation_eq_sum_pairing_concrete ε β hpos
    (2 * S.card) (quarticFreeThermalFieldFamily fun i => d.vertexLabel (order i))
  simpa [quarticFreeThermalOrderedProduct, QuarticDiagram.orderedFreeThermalFieldFamily,
    QuarticDiagram.orderedThermalWickSum, Combinatorics.Pairing.evaluation] using hwick

end
end Bosonic
end SecondQuantization
