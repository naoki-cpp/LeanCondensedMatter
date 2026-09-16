import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ConcreteExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-boson Wick expansion for quartic vertex legs

This module connects the concrete free-boson Gibbs Wick theorem to the quartic diagrammatic leg
convention.  A finite list of quartic vertices is flattened to `4 n = 2 (2 n)` local thermal fields
using the Common quartic-leg equivalence, and the inherited Wick theorem evaluates its normalized
Gibbs expectation as a sum over `Pairing (2 * n)`.

For finite `Mode`, the concrete thermal layer already proves summability and the first-pair
recurrence for every finite ordered field product.  The only analytic hypothesis exposed here is
positivity of each one-mode Boltzmann exponent.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

variable {Mode : Type*}

/-- File-local classical equality keeps the concrete thermal kernel independent of caller choices. -/
local instance instDecidableEqQuarticWickExpansion : DecidableEq Mode := Classical.decEq Mode

/-- Interpret one bosonic quartic local leg as the corresponding free thermal field label. -/
def quarticFreeThermalField (q : QuarticVertexLabel Mode) (l : Fin 4) : FreeThermalField Mode :=
  match Common.quarticLocalLeg q l with
  | .create i => .create i
  | .annihilate i => .annihilate i

/-- The thermal-field realization agrees with the existing quartic local-leg operator. -/
theorem FreeThermalField.operator_quarticFreeThermalField
    (q : QuarticVertexLabel Mode) (l : Fin 4) :
    FreeThermalField.operator (quarticFreeThermalField q l) = quarticLocalLegOperator q l := by
  cases h : Common.quarticLocalLeg q l <;>
    simp [quarticFreeThermalField, quarticLocalLegOperator, Common.quarticLocalLegOperator,
      FreeThermalField.operator, h]

/-- Flatten `n` ordered quartic vertices into their `4 n` free thermal field labels. -/
noncomputable def quarticFreeThermalFieldFamily {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) : Fin (2 * (2 * n)) → FreeThermalField Mode :=
  fun leg =>
    let vl := Common.orderedQuarticLegEquiv n leg
    quarticFreeThermalField (q vl.1) vl.2

/-- Ordered algebraic product of all local legs of a finite list of quartic vertices. -/
noncomputable def quarticFreeThermalOrderedProduct {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  FreeThermalField.orderedProduct (List.ofFn (quarticFreeThermalFieldFamily q))

variable [Fintype Mode]

/-- Finite-order quartic specialization of the concrete free-boson Wick expansion.

The `n` quartic vertices contribute `4 n` local fields, hence the perfect pairings are indexed by
`Pairing (2 * n)`.  The right-hand side uses the shared statistics-independent pairing evaluator. -/
theorem freeGibbsQuarticExpectation_eq_sum_pairing
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) :
    freeGibbsExpectation ε β (quarticFreeThermalOrderedProduct q) =
      ∑ pairing : Pairing (2 * n),
        pairing.evaluation (pairing.weight .boson)
          (fun a b => freeThermalPairValue ε β
            (quarticFreeThermalFieldFamily q a) (quarticFreeThermalFieldFamily q b)) := by
  have hwick := freeGibbsExpectation_eq_sum_pairing_concrete ε β hpos
    (2 * n) (quarticFreeThermalFieldFamily q)
  simpa [quarticFreeThermalOrderedProduct, Combinatorics.Pairing.evaluation] using hwick

end
end Bosonic
end SecondQuantization
