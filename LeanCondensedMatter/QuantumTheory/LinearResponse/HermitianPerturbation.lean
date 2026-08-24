import LeanCondensedMatter.QuantumTheory.LinearResponse.DensityFirstVariation
import Mathlib.Analysis.CStarAlgebra.Basic

set_option linter.style.header false

/-!
# Hermitian time-dependent perturbations

For the general bounded perturbation convention

`H_λ(t) = H₀ + λ V(t)`,

pointwise self-adjointness of `V(t)` is a sufficient physical condition for the first propagator
variation

`K_V(t) = -(i / ℏ) ∫₀ᵗ V_I(s) ds`

to be skew-adjoint. Consequently the first density variation reduces to the Liouville commutator
`[K_V(t), ρ₀]`.

This module records only that sufficient condition. It does not characterize all time-dependent
perturbations whose integrated first variation is skew-adjoint.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- The adjoint operation on bounded operators, bundled as a real-linear isometry. -/
private noncomputable def operatorStarLinearIsometry :
    (H →L[ℂ] H) →ₗᵢ[ℝ] (H →L[ℂ] H) where
  toLinearMap := (starL' ℝ).toLinearEquiv.toLinearMap
  norm_map' := norm_star

@[simp]
private theorem operatorStarLinearIsometry_apply (A : H →L[ℂ] H) :
    operatorStarLinearIsometry A = star A := by
  change (starL' ℝ) A = star A
  exact starL'_apply ℝ A

/-- A pointwise self-adjoint Schrödinger-picture perturbation remains self-adjoint in the
interaction picture. -/
theorem isSelfAdjoint_timeDependentInteractionPerturbation_of_isSelfAdjoint
    (V : ℝ → (H →L[ℂ] H)) (hV : ∀ s, IsSelfAdjoint (V s)) (t : ℝ) :
    IsSelfAdjoint (timeDependentInteractionPerturbation system V t) :=
  isSelfAdjoint_heisenbergEvolution system (V t) (hV t) t

/-- The interval integral of the interaction-picture perturbation is self-adjoint when `V(t)` is
self-adjoint at every time. -/
theorem isSelfAdjoint_integral_timeDependentInteractionPerturbation_of_isSelfAdjoint
    (V : ℝ → (H →L[ℂ] H)) (hV : ∀ s, IsSelfAdjoint (V s)) (t : ℝ) :
    IsSelfAdjoint
      (∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s) := by
  rw [isSelfAdjoint_iff]
  calc
    star (∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s) =
        operatorStarLinearIsometry
          (∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s) := by
      simp
    _ = ∫ s in (0 : ℝ)..t,
          operatorStarLinearIsometry (timeDependentInteractionPerturbation system V s) := by
      symm
      exact LinearIsometry.intervalIntegral_comp_comm
        operatorStarLinearIsometry
        (fun s => timeDependentInteractionPerturbation system V s)
    _ = ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s := by
      apply intervalIntegral.integral_congr
      intro s _
      simpa using
        (isSelfAdjoint_timeDependentInteractionPerturbation_of_isSelfAdjoint
          system V hV s).star_eq

/-- Pointwise self-adjointness of `V(t)` is sufficient for the first propagator variation `K_V(t)`
to be skew-adjoint. -/
theorem star_timeDependentPropagatorFirstVariation_eq_neg_of_isSelfAdjoint
    (V : ℝ → (H →L[ℂ] H)) (hV : ∀ s, IsSelfAdjoint (V s)) (t : ℝ) :
    star (timeDependentPropagatorFirstVariation system V t) =
      -timeDependentPropagatorFirstVariation system V t := by
  have hInt :=
    (isSelfAdjoint_integral_timeDependentInteractionPerturbation_of_isSelfAdjoint
      system V hV t).star_eq
  unfold timeDependentPropagatorFirstVariation
  rw [star_smul, hInt, ← neg_smul]
  congr 1
  rw [Complex.star_def]
  simp
  ring_nf

/-- Under the sufficient physical condition `V(t)† = V(t)`, the first density variation is the
Liouville commutator `[K_V(t), ρ₀]`. -/
theorem densityOperatorFirstVariation_eq_commutator_of_isSelfAdjoint
    (ρ : DensityOperator H) (V : ℝ → (H →L[ℂ] H))
    (hV : ∀ s, IsSelfAdjoint (V s)) (t : ℝ) :
    densityOperatorFirstVariation system ρ V t =
      timeDependentPropagatorFirstVariation system V t * ρ.op -
        ρ.op * timeDependentPropagatorFirstVariation system V t :=
  densityOperatorFirstVariation_eq_commutator_of_star_eq_neg system ρ V t
    (star_timeDependentPropagatorFirstVariation_eq_neg_of_isSelfAdjoint system V hV t)

end
end LinearResponse
end QuantumTheory
