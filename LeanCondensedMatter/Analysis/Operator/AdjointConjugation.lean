module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star

public section

set_option linter.style.header false

/-!
# Adjoint conjugation of bounded operators

This module owns the general real-or-complex bounded-operator operation `T ↦ U T U†` and identities that do not
require `U` to be unitary.
-/

noncomputable section

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- Conjugation of a bounded operator by another bounded operator and its adjoint. -/
@[expose] noncomputable def adjointConjugate (U T : H →L[𝕜] H) : H →L[𝕜] H :=
  U * T * star U

/-- For a differentiable path of bounded operators `U`, the adjoint conjugate of a fixed `T` has
the stated derivative. No unitarity assumption on `U` is needed. -/
theorem hasDerivAt_adjointConjugate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U : ℝ → H →L[ℂ] H} {U' : H →L[ℂ] H} {x : ℝ}
    (hU : HasDerivAt U U' x) (T : H →L[ℂ] H) :
    HasDerivAt (fun s => adjointConjugate (U s) T)
      (U' * T * star (U x) + U x * T * star U') x := by
  simpa only [adjointConjugate, Pi.mul_apply] using (hU.mul_const T).mul hU.star

/-- Adjoint conjugation transports a rank-one operator by applying the conjugating operator to both
vectors. -/
theorem adjointConjugate_rankOne (U : H →L[𝕜] H) (x y : H) :
    adjointConjugate U (InnerProductSpace.rankOne 𝕜 x y) =
      InnerProductSpace.rankOne 𝕜 (U x) (U y) := by
  change (U.comp (InnerProductSpace.rankOne 𝕜 x y)).comp (star U) = _
  rw [InnerProductSpace.comp_rankOne, InnerProductSpace.rankOne_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]

end ContinuousLinearMap
