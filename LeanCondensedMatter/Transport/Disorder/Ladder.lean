import LeanCondensedMatter.Transport.Disorder.BornCommon
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite retarded-advanced Born ladder algebra

This module owns the exact finite-dimensional algebra used by non-crossing vertex corrections.
For a finite disorder ensemble, the retarded-advanced ladder action on a supplied bounded vertex
`Γ` is

```text
L_RA(Γ) = C₂(G₀ᴿ Γ G₀ᴬ),
```

where `C₂ = E[V (·) V]` is the same canonical exact second-moment action used by the Born
self-energy.  The Green operators entering this kernel are the clean finite-ensemble propagators;
using them as a non-self-consistent Born ladder is therefore an approximation choice made by
consumers, not an exact disorder-averaged Green-function claim.

The finite iterates and residual below are exact algebraic objects.  No convergence, inverse of
`1 - L_RA`, Ward identity, SCBA closure, crossed diagram, or thermodynamic limit is asserted here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Retarded-advanced finite Born ladder map
`L_RA(Γ) = C₂(G₀ᴿ Γ G₀ᴬ)` using the same exact second moment as the Born self-energy. -/
noncomputable def retardedAdvancedLadderMap
    (energy broadening : ℝ) (vertex : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.exactSecondMoment
    (ensemble.freeGreen .retarded energy broadening * vertex *
      ensemble.freeGreen .advanced energy broadening)

/-- The RA ladder map is literally the exact second moment of the `G₀ᴿ Γ G₀ᴬ` kernel. -/
theorem retardedAdvancedLadderMap_eq_secondMoment
    (energy broadening : ℝ) (vertex : H →L[ℂ] H) :
    ensemble.retardedAdvancedLadderMap energy broadening vertex =
      ensemble.exactSecondMoment
        (ensemble.freeGreen .retarded energy broadening * vertex *
          ensemble.freeGreen .advanced energy broadening) :=
  rfl

@[simp]
theorem retardedAdvancedLadderMap_zero
    (energy broadening : ℝ) :
    ensemble.retardedAdvancedLadderMap energy broadening 0 = 0 := by
  unfold retardedAdvancedLadderMap FiniteDisorderEnsemble.exactSecondMoment
  simp

/-- Additivity of the exact RA ladder map. -/
theorem retardedAdvancedLadderMap_add
    (energy broadening : ℝ) (left right : H →L[ℂ] H) :
    ensemble.retardedAdvancedLadderMap energy broadening (left + right) =
      ensemble.retardedAdvancedLadderMap energy broadening left +
        ensemble.retardedAdvancedLadderMap energy broadening right := by
  unfold retardedAdvancedLadderMap FiniteDisorderEnsemble.exactSecondMoment
  rw [mul_add, add_mul]
  exact ensemble.exactSecondMomentCLM.map_add _ _

/-- Complex scalar linearity of the exact RA ladder map. -/
theorem retardedAdvancedLadderMap_smul
    (energy broadening : ℝ) (scalar : ℂ) (vertex : H →L[ℂ] H) :
    ensemble.retardedAdvancedLadderMap energy broadening (scalar • vertex) =
      scalar • ensemble.retardedAdvancedLadderMap energy broadening vertex := by
  unfold retardedAdvancedLadderMap FiniteDisorderEnsemble.exactSecondMoment
  rw [mul_smul_comm, smul_mul_assoc]
  exact ensemble.exactSecondMomentCLM.map_smul scalar _

/-- One impurity rung acting on the supplied bare vertex. -/
noncomputable def oneRungVertexCorrection
    (energy broadening : ℝ) (bareVertex : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.retardedAdvancedLadderMap energy broadening bareVertex

/-- Finite non-crossing ladder iterate.  `n = 0` is the bare vertex and each successor performs one
more fixed-point update `Γ ↦ J + L_RA(Γ)`. -/
noncomputable def finiteRALadderVertex
    (energy broadening : ℝ) (bareVertex : H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => bareVertex
  | n + 1 => bareVertex +
      ensemble.retardedAdvancedLadderMap energy broadening
        (ensemble.finiteRALadderVertex energy broadening bareVertex n)

@[simp]
theorem finiteRALadderVertex_zero
    (energy broadening : ℝ) (bareVertex : H →L[ℂ] H) :
    ensemble.finiteRALadderVertex energy broadening bareVertex 0 = bareVertex :=
  rfl

@[simp]
theorem finiteRALadderVertex_succ
    (energy broadening : ℝ) (bareVertex : H →L[ℂ] H) (n : ℕ) :
    ensemble.finiteRALadderVertex energy broadening bareVertex (n + 1) =
      bareVertex + ensemble.retardedAdvancedLadderMap energy broadening
        (ensemble.finiteRALadderVertex energy broadening bareVertex n) :=
  rfl

/-- The first finite ladder update is the bare vertex plus its one-rung correction. -/
theorem finiteRALadderVertex_one
    (energy broadening : ℝ) (bareVertex : H →L[ℂ] H) :
    ensemble.finiteRALadderVertex energy broadening bareVertex 1 =
      bareVertex + ensemble.oneRungVertexCorrection energy broadening bareVertex :=
  rfl

/-- Residual of the RA ladder fixed-point equation `Γ = J + L_RA(Γ)`. -/
noncomputable def raLadderResidual
    (energy broadening : ℝ) (bareVertex dressedVertex : H →L[ℂ] H) : H →L[ℂ] H :=
  dressedVertex - bareVertex -
    ensemble.retardedAdvancedLadderMap energy broadening dressedVertex

/-- Every exact fixed point has vanishing RA ladder residual. -/
theorem raLadderResidual_eq_zero_of_fixedPoint
    (energy broadening : ℝ) (bareVertex dressedVertex : H →L[ℂ] H)
    (hfixed : dressedVertex = bareVertex +
      ensemble.retardedAdvancedLadderMap energy broadening dressedVertex) :
    ensemble.raLadderResidual energy broadening bareVertex dressedVertex = 0 := by
  rw [hfixed]
  simp [raLadderResidual]

/-- Vanishing RA ladder residual is exactly the algebraic fixed-point equation. -/
theorem fixedPoint_of_raLadderResidual_eq_zero
    (energy broadening : ℝ) (bareVertex dressedVertex : H →L[ℂ] H)
    (hresidual : ensemble.raLadderResidual energy broadening bareVertex dressedVertex = 0) :
    dressedVertex = bareVertex +
      ensemble.retardedAdvancedLadderMap energy broadening dressedVertex := by
  unfold raLadderResidual at hresidual
  have hsub :
      dressedVertex - bareVertex =
        ensemble.retardedAdvancedLadderMap energy broadening dressedVertex := by
    exact sub_eq_zero.mp hresidual
  exact (sub_eq_iff_eq_add).mp hsub

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
