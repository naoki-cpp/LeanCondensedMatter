import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.Resolvent
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite retarded-advanced ladder algebra

This module owns the exact finite-dimensional algebra shared by non-crossing vertex corrections.
For a finite disorder ensemble and supplied retarded/advanced Green operators, the ladder action is

```text
L_RA(Γ) = C₂(Gᴿ Γ Gᴬ),
```

where `C₂ = E[V (·) V]` is the same canonical exact second-moment action used by the Born
self-energy. The ladder itself is represented as a bounded complex-linear map, so downstream clean,
SCBA, and other consumers can supply whichever Green operators their approximation requires.

The one-rung correction, finite fixed-point iterates, residual, and conditional resummation below
are exact algebraic objects.  Resummation is available only when `I - L_RA` is supplied as a
continuous linear equivalence.  No convergence, geometric-series expansion, Ward identity, SCBA
closure, crossed diagram, or thermodynamic limit is asserted here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

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

/-- One rung of a supplied finite ladder kernel acting on a bare bounded vertex. -/
noncomputable def oneRungVertexCorrection
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (bareVertex : H →L[ℂ] H) : H →L[ℂ] H :=
  ladder bareVertex

/-- Finite fixed-point ladder iterate.  `n = 0` is the bare vertex and each successor performs the
exact algebraic update `Γ ↦ J + L(Γ)`. -/
noncomputable def finiteLadderVertex
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (bareVertex : H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => bareVertex
  | n + 1 => bareVertex + ladder (finiteLadderVertex ladder bareVertex n)

omit [CompleteSpace H] in
@[simp]
theorem finiteLadderVertex_zero
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (bareVertex : H →L[ℂ] H) :
    finiteLadderVertex ladder bareVertex 0 = bareVertex :=
  rfl

omit [CompleteSpace H] in
@[simp]
theorem finiteLadderVertex_succ
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (bareVertex : H →L[ℂ] H) (n : ℕ) :
    finiteLadderVertex ladder bareVertex (n + 1) =
      bareVertex + ladder (finiteLadderVertex ladder bareVertex n) :=
  rfl

omit [CompleteSpace H] in
/-- The first finite ladder update is the bare vertex plus its one-rung correction. -/
theorem finiteLadderVertex_one
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (bareVertex : H →L[ℂ] H) :
    finiteLadderVertex ladder bareVertex 1 =
      bareVertex + oneRungVertexCorrection ladder bareVertex :=
  rfl

/-- Residual of the finite ladder fixed-point equation `Γ = J + L(Γ)`. -/
noncomputable def ladderResidual
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (bareVertex dressedVertex : H →L[ℂ] H) : H →L[ℂ] H :=
  dressedVertex - bareVertex - ladder dressedVertex

omit [CompleteSpace H] in
/-- Every exact fixed point has vanishing ladder residual. -/
theorem ladderResidual_eq_zero_of_fixedPoint
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (bareVertex dressedVertex : H →L[ℂ] H)
    (hfixed : dressedVertex = bareVertex + ladder dressedVertex) :
    ladderResidual ladder bareVertex dressedVertex = 0 := by
  have h := congrArg (fun vertex =>
    vertex - bareVertex - ladder dressedVertex) hfixed
  simpa [ladderResidual] using h

omit [CompleteSpace H] in
/-- Vanishing ladder residual implies the exact algebraic fixed-point equation. -/
theorem fixedPoint_of_ladderResidual_eq_zero
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (bareVertex dressedVertex : H →L[ℂ] H)
    (hresidual : ladderResidual ladder bareVertex dressedVertex = 0) :
    dressedVertex = bareVertex + ladder dressedVertex := by
  unfold ladderResidual at hresidual
  have hsub : dressedVertex - bareVertex = ladder dressedVertex :=
    sub_eq_zero.mp hresidual
  simpa [add_comm] using (sub_eq_iff_eq_add).mp hsub

/-- Explicit invertibility data for the shifted ladder map `Γ ↦ Γ - L(Γ)`.

Mathlib's `ContinuousLinearEquiv` owns the inverse and its two inverse laws.  The only additional
data retained here is the physical identification of the supplied equivalence with the shifted
ladder action.  This remains an algebraic resummation hypothesis, not a convergence theorem. -/
structure LadderInverseData
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) where
  /-- Supplied continuous-linear equivalence representing `I - L`. -/
  shiftedEquiv : (H →L[ℂ] H) ≃L[ℂ] (H →L[ℂ] H)
  /-- The forward equivalence acts as the shifted ladder map `Γ ↦ Γ - L(Γ)`. -/
  shiftedEquiv_apply : ∀ vertex : H →L[ℂ] H,
    shiftedEquiv vertex = vertex - ladder vertex

/-- Resummed ladder vertex under explicit invertibility of `I - L`. -/
noncomputable def resummedLadderVertex
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (inverseData : LadderInverseData ladder)
    (bareVertex : H →L[ℂ] H) : H →L[ℂ] H :=
  inverseData.shiftedEquiv.symm bareVertex

omit [CompleteSpace H] in
/-- The resummed vertex solves the shifted linear equation `(I - L) Γ = J`. -/
theorem resummedLadderVertex_sub_ladder_eq
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (inverseData : LadderInverseData ladder)
    (bareVertex : H →L[ℂ] H) :
    resummedLadderVertex ladder inverseData bareVertex -
        ladder (resummedLadderVertex ladder inverseData bareVertex) = bareVertex := by
  rw [← inverseData.shiftedEquiv_apply]
  simpa [resummedLadderVertex] using
    inverseData.shiftedEquiv.apply_symm_apply bareVertex

omit [CompleteSpace H] in
/-- The conditional resummation satisfies the exact ladder fixed-point equation. -/
theorem resummedLadderVertex_fixedPoint
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (inverseData : LadderInverseData ladder)
    (bareVertex : H →L[ℂ] H) :
    resummedLadderVertex ladder inverseData bareVertex =
      bareVertex + ladder (resummedLadderVertex ladder inverseData bareVertex) := by
  exact (sub_eq_iff_eq_add).mp
    (resummedLadderVertex_sub_ladder_eq ladder inverseData bareVertex)

omit [CompleteSpace H] in
/-- The named ladder residual vanishes for the conditional resummed vertex. -/
theorem ladderResidual_resummedLadderVertex_eq_zero
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (inverseData : LadderInverseData ladder)
    (bareVertex : H →L[ℂ] H) :
    ladderResidual ladder bareVertex (resummedLadderVertex ladder inverseData bareVertex) = 0 := by
  exact ladderResidual_eq_zero_of_fixedPoint ladder bareVertex _
    (resummedLadderVertex_fixedPoint ladder inverseData bareVertex)

omit [CompleteSpace H] in
/-- Under the same equivalence hypothesis, the ladder fixed point is unique. -/
theorem eq_resummedLadderVertex_of_fixedPoint
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (inverseData : LadderInverseData ladder)
    (bareVertex dressedVertex : H →L[ℂ] H)
    (hfixed : dressedVertex = bareVertex + ladder dressedVertex) :
    dressedVertex = resummedLadderVertex ladder inverseData bareVertex := by
  have hshift : dressedVertex - ladder dressedVertex = bareVertex :=
    (sub_eq_iff_eq_add).mpr hfixed
  have hforward : inverseData.shiftedEquiv dressedVertex = bareVertex := by
    rw [inverseData.shiftedEquiv_apply]
    exact hshift
  calc
    dressedVertex =
        inverseData.shiftedEquiv.symm (inverseData.shiftedEquiv dressedVertex) := by
      exact (inverseData.shiftedEquiv.symm_apply_apply dressedVertex).symm
    _ = inverseData.shiftedEquiv.symm bareVertex := by rw [hforward]
    _ = resummedLadderVertex ladder inverseData bareVertex := rfl

end
end Transport
end QuantumTheory
