import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticWickExpansion
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Ordered
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation

set_option linter.style.header false

/-!
# Convergence-aware bosonic quartic diagram amplitudes

This module places the free-boson thermal pair kernel from the convergence-aware Wick layer on the
existing ordered quartic-diagram structure.  A vertex order turns the diagram labels into a finite
ordered list, and `pairingInOrder` selects one perfect pairing of the resulting local thermal fields.
The scalar diagram value is evaluated through `Combinatorics.Pairing.evaluation`.

The amplitude here is coefficientwise/algebraic.  It includes the quartic coupling product and Dyson
sign, but no ordered-simplex time integration and no completed-space boundedness claim.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

variable {Mode : Type*} {N : ℕ}

/-- The flattened free thermal fields of a bosonic quartic diagram in a chosen vertex order. -/
noncomputable def QuarticDiagram.orderedFreeThermalFieldFamily {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) (order : Common.QuarticVertexOrder S) :
    Fin (2 * (2 * S.card)) → FreeThermalField Mode :=
  quarticFreeThermalFieldFamily (fun i => d.vertexLabel (order i))

/-- The convergence-aware free thermal contraction value of one ordered bosonic quartic diagram. -/
noncomputable def QuarticDiagram.orderedThermalPairingValue [DecidableEq Mode]
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) (order : Common.QuarticVertexOrder S) : ℂ :=
  (d.pairingInOrder order).evaluation
    ((d.pairingInOrder order).weight .boson)
    (fun a b => freeThermalPairValue ε β
      (d.orderedFreeThermalFieldFamily order a)
      (d.orderedFreeThermalFieldFamily order b))

/-- The coefficientwise scalar amplitude of one ordered bosonic quartic diagram, including the
Dyson sign and quartic coupling product. -/
noncomputable def QuarticDiagram.orderedThermalAmplitude [DecidableEq Mode]
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) : ℂ :=
  (-1 : ℂ) ^ S.card * d.vertexWeight g * d.orderedThermalPairingValue ε β order

/-- The full Wick pairing sum for the ordered vertex labels underlying a quartic diagram. -/
noncomputable def QuarticDiagram.orderedThermalWickSum [DecidableEq Mode]
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) (order : Common.QuarticVertexOrder S) : ℂ :=
  ∑ pairing : Pairing (2 * S.card),
    pairing.evaluation (pairing.weight .boson)
      (fun a b => freeThermalPairValue ε β
        (d.orderedFreeThermalFieldFamily order a)
        (d.orderedFreeThermalFieldFamily order b))

variable [Fintype Mode] [DecidableEq Mode]

/-- The convergence-aware Gibbs expectation of the ordered quartic local-leg product is exactly the
sum over the pairing amplitudes carried by the existing quartic diagram combinatorics. -/
theorem QuarticDiagram.freeGibbsExpectation_eq_orderedThermalWickSum
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (admissible : (r : ℕ) → (Fin (2 * r) → FreeThermalField Mode) → Prop)
    (hmem : ∀ (r : ℕ) (C : Fin (2 * r) → FreeThermalField Mode), admissible r C →
      FreeThermalField.orderedProduct (List.ofFn C) ∈ freeGibbsDomain ε β)
    (herase : ∀ (r : ℕ) (C : Fin (2 * (r + 1)) → FreeThermalField Mode), admissible (r + 1) C →
      ∀ j : Fin (2 * r + 1),
        admissible r (fun i : Fin (2 * r) => C ((j.succAbove i).succ)))
    (hrec : ∀ (r : ℕ) (C : Fin (2 * (r + 1)) → FreeThermalField Mode), admissible (r + 1) C →
      (freeGibbsFunctional ε β hpos).value
          (FreeThermalField.orderedProduct (List.ofFn C)) =
        ∑ j : Fin (2 * r + 1),
          freeThermalPairValue ε β (C 0) (C j.succ) *
            (freeGibbsFunctional ε β hpos).value
              (FreeThermalField.orderedProduct
                (List.ofFn fun i : Fin (2 * r) => C ((j.succAbove i).succ))))
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (order : Common.QuarticVertexOrder S)
    (hfields : admissible (2 * S.card) (d.orderedFreeThermalFieldFamily order)) :
    (freeGibbsFunctional ε β hpos).value
        (quarticFreeThermalOrderedProduct (fun i => d.vertexLabel (order i))) =
      d.orderedThermalWickSum ε β order := by
  simpa [QuarticDiagram.orderedFreeThermalFieldFamily,
    QuarticDiagram.orderedThermalWickSum] using
    (freeGibbsQuarticExpectation_eq_sum_pairing ε β hpos admissible hmem herase hrec
      S.card (fun i => d.vertexLabel (order i)) hfields)

end
end Bosonic
end SecondQuantization
