import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option linter.style.header false

/-!
# Adjoint conjugation of bounded operators

This module owns the general bounded-operator operation `T ↦ U T U†` and identities that do not
require `U` to be unitary.
-/

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- Conjugation of a bounded operator by another bounded operator and its adjoint. -/
noncomputable def adjointConjugate (U T : H →L[ℂ] H) : H →L[ℂ] H :=
  U * T * star U

/-- Adjoint conjugation transports a rank-one operator by applying the conjugating operator to both
vectors. -/
theorem adjointConjugate_rankOne (U : H →L[ℂ] H) (x y : H) :
    adjointConjugate U (InnerProductSpace.rankOne ℂ x y) =
      InnerProductSpace.rankOne ℂ (U x) (U y) := by
  ext z
  simp only [adjointConjugate, mul_apply_eq_comp, InnerProductSpace.rankOne_apply, map_smul,
    ContinuousLinearMap.star_eq_adjoint]
  exact congrArg (fun c : ℂ => c • U x)
    (ContinuousLinearMap.adjoint_inner_right U y z)

end ContinuousLinearMap
