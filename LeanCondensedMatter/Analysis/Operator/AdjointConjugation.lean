module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star

public section

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
@[expose] noncomputable def adjointConjugate (U T : H →L[ℂ] H) : H →L[ℂ] H :=
  U * T * star U

/-- For a differentiable path of bounded operators `U`, the adjoint conjugate of a fixed `T` has
the stated derivative. No unitarity assumption on `U` is needed. -/
theorem hasDerivAt_adjointConjugate
    {U : ℝ → H →L[ℂ] H} {U' : H →L[ℂ] H} {x : ℝ}
    (hU : HasDerivAt U U' x) (T : H →L[ℂ] H) :
    HasDerivAt (fun s => adjointConjugate (U s) T)
      (U' * T * star (U x) + U x * T * star U') x := by
  change HasDerivAt (fun s : ℝ => U s * T * star (U s))
    (U' * T * star (U x) + U x * T * star U') x
  have hfun :
      (fun s : ℝ => U s * T) * (fun s => star (U s)) =
        fun s => U s * T * star (U s) := by
    funext s
    simp only [Pi.mul_apply]
  rw [← hfun]
  exact (hU.mul_const T).mul hU.star

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
