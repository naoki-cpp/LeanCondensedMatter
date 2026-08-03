import LeanCondensedMatter.QuantumTheory.DensityOperator.Expectation
import LeanCondensedMatter.QuantumTheory.LinearResponse.TimeDependentPerturbation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star

set_option linter.style.header false

/-!
# First variation of the interaction-picture density operator

For a general bounded time-dependent perturbation

`H_λ(t) = H₀ + λ V(t)`,

define the bounded-operator representative of the perturbed interaction-picture density by

`ρ_λ(t) = U_{I,λ}(t) ρ₀ U_{I,λ}(t)†`.

This module differentiates that expression at zero physical coupling. The first variation is

`K_V(t) ρ₀ + ρ₀ K_V(t)†`,

where

`K_V(t) = -(i / ℏ) ∫₀ᵗ V_I(s) ds`.

When `K_V(t)` is skew-adjoint, this reduces to the Liouville commutator `[K_V(t), ρ₀]`.

The result is deliberately stated in the bounded-operator space. Bundling `ρ_λ(t)` again as a
`DensityOperator` requires unitarity of the propagator, while converting the density variation to
the usual trace formula requires a general non-self-adjoint trace-class ideal. Those are separate
layers.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- The bounded-operator representative of the interaction-picture perturbed density. -/
noncomputable def perturbedDensityOperator
    (ρ : DensityOperator H) (V : ℝ → (H →L[ℂ] H))
    (lam t : ℝ) : H →L[ℂ] H :=
  timeDependentInteractionPropagator system V lam t * ρ.op *
    star (timeDependentInteractionPropagator system V lam t)

/-- The general first variation of `U_{I,λ} ρ₀ U_{I,λ}†` at zero coupling. -/
noncomputable def densityOperatorFirstVariation
    (ρ : DensityOperator H) (V : ℝ → (H →L[ℂ] H))
    (t : ℝ) : H →L[ℂ] H :=
  timeDependentPropagatorFirstVariation system V t * ρ.op +
    ρ.op * star (timeDependentPropagatorFirstVariation system V t)

@[simp]
theorem perturbedDensityOperator_zero_coupling
    (ρ : DensityOperator H) (V : ℝ → (H →L[ℂ] H)) (t : ℝ) :
    perturbedDensityOperator system ρ V 0 t = ρ.op := by
  simp [perturbedDensityOperator]

/-- The interaction-picture density representative is differentiable at zero coupling, with first
variation `K_V ρ₀ + ρ₀ K_V†`. -/
theorem hasDerivAt_perturbedDensityOperator_zero_of_bound
    (ρ : DensityOperator H)
    {V : ℝ → (H →L[ℂ] H)} {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Set.Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Set.Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => perturbedDensityOperator system ρ V lam t)
      (densityOperatorFirstVariation system ρ V t)
      0 := by
  have hU : HasDerivAt
      (fun lam : ℝ => timeDependentInteractionPropagator system V lam t)
      (timeDependentPropagatorFirstVariation system V t)
      0 :=
    hasDerivAt_timeDependentInteractionPropagator_zero_of_bound system hM hV ht
  have hUstar : HasDerivAt
      (fun lam : ℝ => star (timeDependentInteractionPropagator system V lam t))
      (star (timeDependentPropagatorFirstVariation system V t))
      0 := by
    simpa [Function.comp_def] using hU.star
  have hleft := hU.mul_const ρ.op
  have hprod := hleft.mul hUstar
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at hprod
  simpa [perturbedDensityOperator, densityOperatorFirstVariation] using hprod

/-- If the first propagator variation is skew-adjoint, the density variation is its commutator with
`ρ₀`. -/
theorem densityOperatorFirstVariation_eq_commutator_of_star_eq_neg
    (ρ : DensityOperator H) (V : ℝ → (H →L[ℂ] H)) (t : ℝ)
    (hK : star (timeDependentPropagatorFirstVariation system V t) =
      -timeDependentPropagatorFirstVariation system V t) :
    densityOperatorFirstVariation system ρ V t =
      timeDependentPropagatorFirstVariation system V t * ρ.op -
        ρ.op * timeDependentPropagatorFirstVariation system V t := by
  simp [densityOperatorFirstVariation, hK, sub_eq_add_neg]

end
end LinearResponse
end QuantumTheory
