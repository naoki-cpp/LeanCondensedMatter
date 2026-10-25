import LeanCondensedMatter.QuantumTheory.LinearResponse.Perturbation.TimeDependent
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative

set_option linter.style.header false

/-!
# Hermitian time-dependent perturbations

For the general bounded perturbation convention

`H_λ(t) = H₀ + λ V(t)`,

pointwise self-adjointness of `V(t)` is a sufficient physical condition for the first propagator
variation

`K_V(t) = -(i / ℏ) ∫₀ᵗ V_I(s) ds`

to be skew-adjoint.

This module records only that sufficient condition; density-operator consequences live in
`Perturbation.DensityFirstVariation`. It does not characterize all time-dependent
perturbations whose integrated first variation is skew-adjoint.
-/

namespace QuantumTheory
namespace LinearResponse

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)

/-- A pointwise self-adjoint Schrödinger-picture perturbation remains self-adjoint in the
interaction picture. -/
theorem isSelfAdjoint_timeDependentInteractionPerturbation_of_isSelfAdjoint
    (V : ℝ → (H →L[ℂ] H)) (hV : ∀ s, IsSelfAdjoint (V s)) (t : ℝ) :
    IsSelfAdjoint (timeDependentInteractionPerturbation U V t) := by
  change IsSelfAdjoint (heisenbergEvolution U t (V t))
  rw [isSelfAdjoint_iff, ← map_star, (hV t).star_eq]

/-- The interval integral of the interaction-picture perturbation is self-adjoint when `V(t)` is
self-adjoint at every time. -/
theorem isSelfAdjoint_integral_timeDependentInteractionPerturbation_of_isSelfAdjoint
    (V : ℝ → (H →L[ℂ] H)) (hV : ∀ s, IsSelfAdjoint (V s)) (t : ℝ) :
    IsSelfAdjoint
      (∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation U V s) := by
  rw [isSelfAdjoint_iff]
  calc
    star (∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation U V s) =
        ∫ s in (0 : ℝ)..t, star (timeDependentInteractionPerturbation U V s) :=
      ((starₗᵢ ℝ).toLinearIsometry.intervalIntegral_comp_comm
        (fun s => timeDependentInteractionPerturbation U V s)).symm
    _ = ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation U V s := by
      apply intervalIntegral.integral_congr
      intro s _
      exact
        (isSelfAdjoint_timeDependentInteractionPerturbation_of_isSelfAdjoint U V hV s).star_eq

/-- Pointwise self-adjointness of `V(t)` is sufficient for the first propagator variation `K_V(t)`
to be skew-adjoint. -/
theorem star_timeDependentPropagatorFirstVariation_eq_neg_of_isSelfAdjoint
    (V : ℝ → (H →L[ℂ] H)) (hV : ∀ s, IsSelfAdjoint (V s)) (t : ℝ) :
    star (timeDependentPropagatorFirstVariation U hbar V t) =
      -timeDependentPropagatorFirstVariation U hbar V t := by
  have hInt :=
    (isSelfAdjoint_integral_timeDependentInteractionPerturbation_of_isSelfAdjoint U V hV t).star_eq
  unfold timeDependentPropagatorFirstVariation
  rw [star_smul, hInt, ← neg_smul]
  congr 1
  rw [Complex.star_def]
  simp
  ring_nf


end
end LinearResponse
end QuantumTheory
