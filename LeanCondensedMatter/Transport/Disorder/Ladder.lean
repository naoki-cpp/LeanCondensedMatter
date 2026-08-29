import LeanCondensedMatter.Transport.Disorder.BornCommon
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
self-energy.  The ladder itself is represented as a bounded complex-linear map.  The convenience
specialization `freeRetardedAdvancedLadderCLM` inserts the clean finite-ensemble Green operators;
SCBA and other consumers can reuse the same owner with their own supplied Green operators.

The one-rung correction, finite fixed-point iterates, and residual below are exact algebraic
objects.  No convergence, inverse of `1 - L_RA`, Ward identity, SCBA closure, crossed diagram, or
thermodynamic limit is asserted here.
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

/-- Non-self-consistent Born RA ladder obtained by inserting the clean finite-ensemble Green
operators.  This specialization is an approximation choice for later physical consumers; the
underlying covariance action remains exact finite-ensemble data. -/
noncomputable def freeRetardedAdvancedLadderCLM
    (energy broadening : ℝ) : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ensemble.retardedAdvancedLadderCLM
    (ensemble.freeGreen .retarded energy broadening)
    (ensemble.freeGreen .advanced energy broadening)

/-- The clean RA specialization evaluates to
`C₂(G₀ᴿ Γ G₀ᴬ)`. -/
@[simp]
theorem freeRetardedAdvancedLadderCLM_apply
    (energy broadening : ℝ) (vertex : H →L[ℂ] H) :
    ensemble.freeRetardedAdvancedLadderCLM energy broadening vertex =
      ensemble.exactSecondMoment
        (ensemble.freeGreen .retarded energy broadening * vertex *
          ensemble.freeGreen .advanced energy broadening) :=
  rfl

@[simp]
theorem freeRetardedAdvancedLadderCLM_zero
    (energy broadening : ℝ) :
    ensemble.freeRetardedAdvancedLadderCLM energy broadening 0 = 0 := by
  exact (ensemble.freeRetardedAdvancedLadderCLM energy broadening).map_zero

/-- Additivity of the clean RA ladder specialization. -/
theorem freeRetardedAdvancedLadderCLM_add
    (energy broadening : ℝ) (left right : H →L[ℂ] H) :
    ensemble.freeRetardedAdvancedLadderCLM energy broadening (left + right) =
      ensemble.freeRetardedAdvancedLadderCLM energy broadening left +
        ensemble.freeRetardedAdvancedLadderCLM energy broadening right := by
  exact (ensemble.freeRetardedAdvancedLadderCLM energy broadening).map_add left right

/-- Complex scalar linearity of the clean RA ladder specialization. -/
theorem freeRetardedAdvancedLadderCLM_smul
    (energy broadening : ℝ) (scalar : ℂ) (vertex : H →L[ℂ] H) :
    ensemble.freeRetardedAdvancedLadderCLM energy broadening (scalar • vertex) =
      scalar • ensemble.freeRetardedAdvancedLadderCLM energy broadening vertex := by
  exact (ensemble.freeRetardedAdvancedLadderCLM energy broadening).map_smul scalar vertex

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

@[simp]
theorem finiteLadderVertex_zero
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (bareVertex : H →L[ℂ] H) :
    finiteLadderVertex ladder bareVertex 0 = bareVertex :=
  rfl

@[simp]
theorem finiteLadderVertex_succ
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (bareVertex : H →L[ℂ] H) (n : ℕ) :
    finiteLadderVertex ladder bareVertex (n + 1) =
      bareVertex + ladder (finiteLadderVertex ladder bareVertex n) :=
  rfl

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

/-- Every exact fixed point has vanishing ladder residual. -/
theorem ladderResidual_eq_zero_of_fixedPoint
    (ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (bareVertex dressedVertex : H →L[ℂ] H)
    (hfixed : dressedVertex = bareVertex + ladder dressedVertex) :
    ladderResidual ladder bareVertex dressedVertex = 0 := by
  rw [hfixed]
  simp [ladderResidual]

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

end
end Transport
end QuantumTheory
