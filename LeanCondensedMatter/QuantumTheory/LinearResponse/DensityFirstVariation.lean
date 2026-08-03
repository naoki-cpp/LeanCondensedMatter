import LeanCondensedMatter.QuantumTheory.DensityOperator.Expectation
import LeanCondensedMatter.QuantumTheory.LinearResponse.FirstVariation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star

set_option linter.style.header false

/-!
# First variation of the interaction-picture density operator

For the interaction-picture propagator `U_λ(t)`, define the bounded-operator representative of the
perturbed density by

`ρ_λ(t) = U_λ(t) ρ₀ U_λ(t)†`.

This module differentiates that expression at zero physical coupling. For a general bounded
perturbation the first variation is

`K(t) ρ₀ + ρ₀ K(t)†`,

where `K(t) = (i / ℏ) ∫₀ᵗ V_I(s) ds` is the first propagator variation. When `K(t)` is skew-adjoint,
this reduces to the Liouville commutator `[K(t), ρ₀]`.

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

/-- The first interaction-picture propagator variation
`K(t) = (i / ℏ) ∫₀ᵗ V_I(s) ds`. -/
noncomputable def interactionPropagatorFirstVariation
    (B : H →L[ℂ] H) (f : ℝ → ℝ) (t : ℝ) : H →L[ℂ] H :=
  (Complex.I / (system.hbar : ℂ)) •
    ∫ s in (0 : ℝ)..t, interactionPerturbation system B f s

/-- The bounded-operator representative of the interaction-picture perturbed density. -/
noncomputable def perturbedDensityOperator
    (ρ : DensityOperator H) (B : H →L[ℂ] H) (f : ℝ → ℝ)
    (lam t : ℝ) : H →L[ℂ] H :=
  interactionPropagator system B f lam t * ρ.op *
    star (interactionPropagator system B f lam t)

/-- The general first variation of `U_λ ρ₀ U_λ†` at zero coupling. -/
noncomputable def densityOperatorFirstVariation
    (ρ : DensityOperator H) (B : H →L[ℂ] H) (f : ℝ → ℝ)
    (t : ℝ) : H →L[ℂ] H :=
  interactionPropagatorFirstVariation system B f t * ρ.op +
    ρ.op * star (interactionPropagatorFirstVariation system B f t)

@[simp]
theorem perturbedDensityOperator_zero_coupling
    (ρ : DensityOperator H) (B : H →L[ℂ] H) (f : ℝ → ℝ) (t : ℝ) :
    perturbedDensityOperator system ρ B f 0 t = ρ.op := by
  simp [perturbedDensityOperator]

/-- Repackage the propagator first-variation theorem using the named first-variation operator. -/
theorem hasDerivAt_interactionPropagator_zero_of_bound'
    {B : H →L[ℂ] H} {f : ℝ → ℝ}
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Set.Icc (0 : ℝ) β, ‖interactionPerturbation system B f s‖ ≤ M)
    (ht : t ∈ Set.Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => interactionPropagator system B f lam t)
      (interactionPropagatorFirstVariation system B f t)
      0 := by
  simpa [interactionPropagatorFirstVariation] using
    hasDerivAt_interactionPropagator_zero_of_bound system hM hV ht

/-- The interaction-picture density representative is differentiable at zero coupling, with first
variation `Kρ₀ + ρ₀K†`. -/
theorem hasDerivAt_perturbedDensityOperator_zero_of_bound
    (ρ : DensityOperator H)
    {B : H →L[ℂ] H} {f : ℝ → ℝ}
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Set.Icc (0 : ℝ) β, ‖interactionPerturbation system B f s‖ ≤ M)
    (ht : t ∈ Set.Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => perturbedDensityOperator system ρ B f lam t)
      (densityOperatorFirstVariation system ρ B f t)
      0 := by
  have hU : HasDerivAt
      (fun lam : ℝ => interactionPropagator system B f lam t)
      (interactionPropagatorFirstVariation system B f t)
      0 :=
    hasDerivAt_interactionPropagator_zero_of_bound' system hM hV ht
  have hUstar : HasDerivAt
      (fun lam : ℝ => star (interactionPropagator system B f lam t))
      (star (interactionPropagatorFirstVariation system B f t))
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
    (ρ : DensityOperator H) (B : H →L[ℂ] H) (f : ℝ → ℝ) (t : ℝ)
    (hK : star (interactionPropagatorFirstVariation system B f t) =
      -interactionPropagatorFirstVariation system B f t) :
    densityOperatorFirstVariation system ρ B f t =
      interactionPropagatorFirstVariation system B f t * ρ.op -
        ρ.op * interactionPropagatorFirstVariation system B f t := by
  simp [densityOperatorFirstVariation, hK, sub_eq_add_neg]

end
end LinearResponse
end QuantumTheory
