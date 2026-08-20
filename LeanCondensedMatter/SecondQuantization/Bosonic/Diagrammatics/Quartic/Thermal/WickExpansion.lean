import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg

set_option linter.style.header false

/-!
# Free-boson Wick expansion for quartic vertex legs

This module connects the convergence-aware free-boson Wick recursion to the quartic diagrammatic
leg convention.  A finite list of quartic vertices is flattened to `4 n = 2 (2 n)` local thermal
fields using the Common quartic-leg equivalence, and the inherited Wick theorem evaluates its
normalized Gibbs expectation as a sum over `Pairing (2 * n)`.

The analytic hypotheses remain explicit through the admissibility predicate and first-pair
recurrence.  No finite occupation basis or completed-space boundedness assumption is introduced.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

variable {Mode : Type*}

/-- Interpret one bosonic quartic local leg as the corresponding free thermal field label. -/
def quarticFreeThermalField (q : QuarticVertexLabel Mode) (l : Fin 4) : FreeThermalField Mode :=
  if Common.quarticLocalLegIsCreate l then
    .create (Common.quarticLocalLegMode q l)
  else
    .annihilate (Common.quarticLocalLegMode q l)

/-- The thermal-field realization agrees with the existing quartic local-leg operator. -/
theorem FreeThermalField.operator_quarticFreeThermalField
    (q : QuarticVertexLabel Mode) (l : Fin 4) :
    FreeThermalField.operator (quarticFreeThermalField q l) = quarticLocalLegOperator q l := by
  fin_cases l <;>
    simp [quarticFreeThermalField, quarticLocalLegOperator, FreeThermalField.operator,
      Common.quarticLocalLegIsCreate, Common.quarticLocalLegMode,
      Common.quarticLocalLegOperator]

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

variable [Fintype Mode] [DecidableEq Mode]

/-- Finite-order quartic specialization of the convergence-aware free-boson Wick expansion.

The `n` quartic vertices contribute `4 n` local fields, hence the perfect pairings are indexed by
`Pairing (2 * n)`.  The right-hand side uses the shared statistics-independent pairing evaluator. -/
theorem freeGibbsQuarticExpectation_eq_sum_pairing
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
    (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (hq : admissible (2 * n) (quarticFreeThermalFieldFamily q)) :
    (freeGibbsFunctional ε β hpos).value (quarticFreeThermalOrderedProduct q) =
      ∑ pairing : Pairing (2 * n),
        pairing.evaluation (pairing.weight .boson)
          (fun a b => freeThermalPairValue ε β
            (quarticFreeThermalFieldFamily q a) (quarticFreeThermalFieldFamily q b)) := by
  have hwick := freeGibbsExpectation_eq_sum_pairing ε β hpos admissible hmem herase hrec
    (2 * n) (quarticFreeThermalFieldFamily q) hq
  simpa [quarticFreeThermalOrderedProduct, Combinatorics.Pairing.evaluation] using hwick

end
end Bosonic
end SecondQuantization
