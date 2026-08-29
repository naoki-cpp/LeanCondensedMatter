import LeanCondensedMatter.Transport.Disorder.BornCommon
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact finite Born retarded–advanced ladder algebra

This module owns the reusable retarded–advanced ladder algebra built from the same canonical exact
finite-disorder second moment used by the first-Born self-energy.  At fixed energy and broadening,

```text
L_RA(Γ) = C₂(G₀ᴿ Γ G₀ᴬ).
```

The ladder map is represented as a bounded complex-linear map, so linearity is part of the object
rather than a separately supplied assumption.  Finite iterates start from a supplied bare bounded
vertex `J` and obey

```text
Γ₀ = J,
Γₙ₊₁ = J + L_RA(Γₙ).
```

The named residual

```text
R(Γ) = Γ - J - L_RA(Γ)
```

vanishes exactly at a ladder fixed point.

The use of clean retarded/advanced Green operators makes this the non-self-consistent Born ladder.
No infinite resummation, inverse hypothesis, SCBA propagator, Ward identity, conductivity theorem,
crossed diagram, or thermodynamic/zero-broadening limit is introduced here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Canonical non-self-consistent Born retarded–advanced ladder map
`Γ ↦ C₂(G₀ᴿ Γ G₀ᴬ)`, built from the same exact finite second-moment action as the Born self-energy. -/
noncomputable def bornRetardedAdvancedLadderMap
    (energy broadening : ℝ) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ensemble.exactSecondMomentCLM.comp
    ((ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H))
      (ensemble.freeGreen .retarded energy broadening)
      (ensemble.freeGreen .advanced energy broadening))

/-- The Born RA ladder map is exactly the canonical second moment applied to the clean
retarded–vertex–advanced product. -/
@[simp]
theorem bornRetardedAdvancedLadderMap_apply
    (energy broadening : ℝ) (vertex : H →L[ℂ] H) :
    ensemble.bornRetardedAdvancedLadderMap energy broadening vertex =
      ensemble.exactSecondMoment
        (ensemble.freeGreen .retarded energy broadening * vertex *
          ensemble.freeGreen .advanced energy broadening) := by
  rfl

/-- One impurity-ladder rung acting on a supplied bare bounded vertex. -/
noncomputable def bornRetardedAdvancedOneRungCorrection
    (energy broadening : ℝ) (bareVertex : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.bornRetardedAdvancedLadderMap energy broadening bareVertex

/-- Finite fixed-point iteration of the Born RA ladder beginning from the bare vertex.  The value at
`n` contains the bare vertex plus ladder contributions through at most `n` rungs. -/
noncomputable def bornRetardedAdvancedLadderIterate
    (energy broadening : ℝ) (bareVertex : H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => bareVertex
  | n + 1 =>
      bareVertex +
        ensemble.bornRetardedAdvancedLadderMap energy broadening
          (bornRetardedAdvancedLadderIterate energy broadening bareVertex n)

@[simp]
theorem bornRetardedAdvancedLadderIterate_zero
    (energy broadening : ℝ) (bareVertex : H →L[ℂ] H) :
    ensemble.bornRetardedAdvancedLadderIterate energy broadening bareVertex 0 = bareVertex :=
  rfl

@[simp]
theorem bornRetardedAdvancedLadderIterate_succ
    (energy broadening : ℝ) (bareVertex : H →L[ℂ] H) (n : ℕ) :
    ensemble.bornRetardedAdvancedLadderIterate energy broadening bareVertex (n + 1) =
      bareVertex +
        ensemble.bornRetardedAdvancedLadderMap energy broadening
          (ensemble.bornRetardedAdvancedLadderIterate energy broadening bareVertex n) :=
  rfl

/-- The first finite iterate is the bare vertex plus the one-rung correction. -/
theorem bornRetardedAdvancedLadderIterate_one
    (energy broadening : ℝ) (bareVertex : H →L[ℂ] H) :
    ensemble.bornRetardedAdvancedLadderIterate energy broadening bareVertex 1 =
      bareVertex +
        ensemble.bornRetardedAdvancedOneRungCorrection energy broadening bareVertex := by
  rfl

/-- Residual of the Born RA ladder fixed-point equation for a supplied bare vertex. -/
noncomputable def bornRetardedAdvancedLadderResidual
    (energy broadening : ℝ) (bareVertex candidate : H →L[ℂ] H) : H →L[ℂ] H :=
  candidate - bareVertex -
    ensemble.bornRetardedAdvancedLadderMap energy broadening candidate

/-- Vanishing of the ladder residual is exactly the fixed-point equation
`Γ = J + L_RA(Γ)`. -/
theorem bornRetardedAdvancedLadderResidual_eq_zero_iff
    (energy broadening : ℝ) (bareVertex candidate : H →L[ℂ] H) :
    ensemble.bornRetardedAdvancedLadderResidual
        energy broadening bareVertex candidate = 0 ↔
      candidate = bareVertex +
        ensemble.bornRetardedAdvancedLadderMap energy broadening candidate := by
  constructor
  · intro hresidual
    have hdiff :
        candidate - bareVertex =
          ensemble.bornRetardedAdvancedLadderMap energy broadening candidate := by
      apply sub_eq_zero.mp
      simpa only [bornRetardedAdvancedLadderResidual] using hresidual
    calc
      candidate = (candidate - bareVertex) + bareVertex := by
        abel
      _ = ensemble.bornRetardedAdvancedLadderMap energy broadening candidate + bareVertex := by
        rw [hdiff]
      _ = bareVertex +
          ensemble.bornRetardedAdvancedLadderMap energy broadening candidate := by
        abel
  · intro hfixed
    have hdiff :
        candidate - bareVertex =
          ensemble.bornRetardedAdvancedLadderMap energy broadening candidate := by
      calc
        candidate - bareVertex =
            (bareVertex +
              ensemble.bornRetardedAdvancedLadderMap energy broadening candidate) - bareVertex := by
          exact congrArg (fun vertex : H →L[ℂ] H => vertex - bareVertex) hfixed
        _ = ensemble.bornRetardedAdvancedLadderMap energy broadening candidate := by
          abel
    unfold bornRetardedAdvancedLadderResidual
    rw [hdiff]
    exact sub_self _

/-- If two consecutive finite ladder iterates coincide, that iterate is already an exact algebraic
fixed point of the Born RA ladder. -/
theorem bornRetardedAdvancedLadderResidual_iterate_eq_zero_of_stable
    (energy broadening : ℝ) (bareVertex : H →L[ℂ] H) (n : ℕ)
    (hstable :
      ensemble.bornRetardedAdvancedLadderIterate energy broadening bareVertex (n + 1) =
        ensemble.bornRetardedAdvancedLadderIterate energy broadening bareVertex n) :
    ensemble.bornRetardedAdvancedLadderResidual energy broadening bareVertex
        (ensemble.bornRetardedAdvancedLadderIterate energy broadening bareVertex n) = 0 := by
  rw [ensemble.bornRetardedAdvancedLadderResidual_eq_zero_iff]
  calc
    ensemble.bornRetardedAdvancedLadderIterate energy broadening bareVertex n =
        ensemble.bornRetardedAdvancedLadderIterate energy broadening bareVertex (n + 1) :=
      hstable.symm
    _ = bareVertex +
        ensemble.bornRetardedAdvancedLadderMap energy broadening
          (ensemble.bornRetardedAdvancedLadderIterate energy broadening bareVertex n) :=
      ensemble.bornRetardedAdvancedLadderIterate_succ energy broadening bareVertex n

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
