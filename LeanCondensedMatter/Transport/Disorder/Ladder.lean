import LeanCondensedMatter.Transport.Disorder.Moments

set_option linter.style.header false

/-!
# Retarded-advanced ladder algebra

This module owns the bounded algebra shared by non-crossing vertex corrections. For a finite
disorder ensemble and supplied retarded/advanced Green operators, the ladder action is

```text
L_RA(Γ) = C₂(Gᴿ Γ Gᴬ),
```

where `C₂ = E[V (·) V]` is the same canonical exact second-moment action used by the Born
self-energy. The ladder itself is represented as a bounded complex-linear map, so downstream clean,
SCBA, and other consumers can supply whichever Green operators their approximation requires.

The public algebra is intentionally small: the RA kernel, finite fixed-point iterates, and
conditional resummation when `I - L_RA` is a unit. No convergence, geometric-series expansion, Ward
identity, SCBA closure, crossed diagram, or thermodynamic limit is asserted here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

namespace FiniteDisorderEnsemble

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]
variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Finite covariance ladder map `Γ ↦ C₂(Gᴿ Γ Gᴬ)` for supplied left/right Green operators.
The same exact second moment owns both this map and the finite Born self-energy. -/
noncomputable def retardedAdvancedLadderCLM
    (retardedGreen advancedGreen : H →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ensemble.exactSecondMomentCLM.comp
    ((ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H)) retardedGreen advancedGreen)

/-- Evaluation of the finite covariance ladder is the expected operator insertion
`C₂(Gᴿ Γ Gᴬ)`. -/
@[simp]
theorem retardedAdvancedLadderCLM_apply
    (retardedGreen advancedGreen vertex : H →L[ℂ] H) :
    ensemble.retardedAdvancedLadderCLM retardedGreen advancedGreen vertex =
      ensemble.exactSecondMoment (retardedGreen * vertex * advancedGreen) :=
  rfl

end FiniteDisorderEnsemble

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Finite fixed-point ladder iterate. `n = 0` is the bare vertex and each successor performs the
exact algebraic update `Γ ↦ J + L(Γ)`. -/
noncomputable def finiteLadderVertex
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (bareVertex : H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => bareVertex
  | n + 1 => bareVertex + ladder (finiteLadderVertex ladder bareVertex n)

/-- Resummed ladder vertex when the shifted ladder endomorphism `I - L` is a unit. -/
noncomputable def resummedLadderVertex
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hinvertible : IsUnit (1 - ladder))
    (bareVertex : H →L[ℂ] H) : H →L[ℂ] H :=
  (↑(hinvertible.unit⁻¹) : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) bareVertex

private theorem shiftedLadder_apply_resummedLadderVertex
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hinvertible : IsUnit (1 - ladder))
    (bareVertex : H →L[ℂ] H) :
    (1 - ladder) (resummedLadderVertex ladder hinvertible bareVertex) = bareVertex := by
  let inverse : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) := ↑(hinvertible.unit⁻¹)
  have hmul : (1 - ladder) * inverse = 1 := by
    simpa [inverse] using hinvertible.mul_val_inv
  change ((1 - ladder) * inverse) bareVertex = bareVertex
  rw [hmul]
  simp

/-- The conditional resummation satisfies the exact ladder fixed-point equation. -/
theorem resummedLadderVertex_fixedPoint
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hinvertible : IsUnit (1 - ladder))
    (bareVertex : H →L[ℂ] H) :
    resummedLadderVertex ladder hinvertible bareVertex =
      bareVertex + ladder (resummedLadderVertex ladder hinvertible bareVertex) := by
  apply (sub_eq_iff_eq_add).mp
  simpa using
    shiftedLadder_apply_resummedLadderVertex ladder hinvertible bareVertex

/-- When `I - L` is a unit, the ladder fixed point is unique. -/
theorem eq_resummedLadderVertex_of_fixedPoint
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hinvertible : IsUnit (1 - ladder))
    (bareVertex dressedVertex : H →L[ℂ] H)
    (hfixed : dressedVertex = bareVertex + ladder dressedVertex) :
    dressedVertex = resummedLadderVertex ladder hinvertible bareVertex := by
  let inverse : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) := ↑(hinvertible.unit⁻¹)
  have hleft : inverse * (1 - ladder) = 1 := by
    simpa [inverse] using hinvertible.val_inv_mul
  have hinjective : Function.Injective
      ((1 - ladder) : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) := by
    intro left right heq
    have hleftApply : inverse ((1 - ladder) left) = left := by
      change (inverse * (1 - ladder)) left = left
      rw [hleft]
      simp
    have hrightApply : inverse ((1 - ladder) right) = right := by
      change (inverse * (1 - ladder)) right = right
      rw [hleft]
      simp
    calc
      left = inverse ((1 - ladder) left) := hleftApply.symm
      _ = inverse ((1 - ladder) right) := congrArg inverse heq
      _ = right := hrightApply
  apply hinjective
  have hdressed : (1 - ladder) dressedVertex = bareVertex := by
    have hshift : dressedVertex - ladder dressedVertex = bareVertex :=
      (sub_eq_iff_eq_add).mpr hfixed
    simpa using hshift
  calc
    (1 - ladder) dressedVertex = bareVertex := hdressed
    _ = (1 - ladder) (resummedLadderVertex ladder hinvertible bareVertex) :=
      (shiftedLadder_apply_resummedLadderVertex ladder hinvertible bareVertex).symm

end
end Transport
end QuantumTheory
