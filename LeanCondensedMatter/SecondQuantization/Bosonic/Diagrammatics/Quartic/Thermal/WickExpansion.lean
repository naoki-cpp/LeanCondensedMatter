import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg

set_option linter.style.header false

/-!
# Free-boson thermal fields for quartic vertex legs

This module connects the bosonic quartic diagrammatic leg convention to the free thermal-field
representation.  A finite list of quartic vertices is flattened to `4 n = 2 (2 n)` local thermal
fields using the Common quartic-leg equivalence, and their ordered algebraic product is exposed for
downstream thermal expectations.

The concrete Gibbs/Wick theorem is owned by the bosonic thermal layer and is consumed directly at
the diagram-amplitude boundary rather than being wrapped here.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*}

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

end
end Bosonic
end SecondQuantization
