import LeanCondensedMatter.Analysis.Dyson.FirstVariation
import LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option linter.style.header false

/-!
# General bounded time-dependent perturbations

This module treats a general bounded time-dependent perturbation

`H_λ(t) = H₀ + λ V(t)`

without assuming a separated source form such as `f(t) B`. Its interaction-picture representative is

`V_I(t) = U₀(-t) V(t) U₀(t)`.

The generic Dyson recursion uses `Dₙ₊₁(t) = -∫₀ᵗ V_I(s) Dₙ(s) ds`, so the physical scalar coupling
is `λ i / ℏ`. Consequently the first propagator variation is

`K_V(t) = -(i / ℏ) ∫₀ᵗ V_I(s) ds`.

Source-coupled perturbations are downstream specializations obtained by choosing, for example,
`V(t) = -f(t) B`.
-/

namespace QuantumTheory
namespace LinearResponse

open Filter Set
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- The interaction-picture form `V_I(t) = U₀(-t) V(t) U₀(t)` of a general time-dependent
bounded perturbation. -/
noncomputable def timeDependentInteractionPerturbation
    (V : ℝ → (H →L[ℂ] H)) (t : ℝ) : H →L[ℂ] H :=
  heisenbergEvolution system (V t) t

/-- The generic Dyson scalar corresponding to `H_λ(t) = H₀ + λ V(t)`. -/
noncomputable def timeDependentPhysicalDysonCoupling (lam : ℝ) : ℂ :=
  (lam : ℂ) * (Complex.I / (system.hbar : ℂ))

/-- The norm of the physical scalar coupling is `|λ| / ℏ`. -/
theorem norm_timeDependentPhysicalDysonCoupling (lam : ℝ) :
    ‖timeDependentPhysicalDysonCoupling system lam‖ = |lam| / system.hbar := by
  simp [timeDependentPhysicalDysonCoupling, abs_of_pos system.hbar_pos, div_eq_mul_inv]

/-- The interaction-picture propagator for the general perturbation `H₀ + λ V(t)`. -/
noncomputable def timeDependentInteractionPropagator
    (V : ℝ → (H →L[ℂ] H)) (lam t : ℝ) : H →L[ℂ] H :=
  Dyson.evolution (timeDependentInteractionPerturbation system V)
    (timeDependentPhysicalDysonCoupling system lam) t

/-- The first propagator variation
`K_V(t) = -(i / ℏ) ∫₀ᵗ V_I(s) ds`. -/
noncomputable def timeDependentPropagatorFirstVariation
    (V : ℝ → (H →L[ℂ] H)) (t : ℝ) : H →L[ℂ] H :=
  (-(Complex.I / (system.hbar : ℂ))) •
    ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s

@[simp]
theorem timeDependentInteractionPropagator_zero_coupling
    (V : ℝ → (H →L[ℂ] H)) (t : ℝ) :
    timeDependentInteractionPropagator system V 0 t = 1 := by
  simpa [timeDependentInteractionPropagator, timeDependentPhysicalDysonCoupling] using
    Dyson.evolution_zero_coupling (timeDependentInteractionPerturbation system V) t

/-- The exact first weighted Dyson term for `H₀ + λ V(t)`. -/
theorem timeDependentDysonTerm_one
    (V : ℝ → (H →L[ℂ] H)) (lam t : ℝ) :
    Dyson.term (timeDependentInteractionPerturbation system V)
        (timeDependentPhysicalDysonCoupling system lam) t 1 =
      ((lam : ℂ) * (-(Complex.I / (system.hbar : ℂ)))) •
        ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s := by
  rw [Dyson.term_one]
  congr 1
  simp [timeDependentPhysicalDysonCoupling]

/-- After subtracting the identity and exact first term, the propagator remainder starts at order
`λ²`. -/
theorem norm_timeDependentInteractionPropagator_sub_firstOrder_le_of_bound
    {V : ℝ → (H →L[ℂ] H)} {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) (lam : ℝ) :
    ‖timeDependentInteractionPropagator system V lam t -
        (1 + ((lam : ℂ) * (-(Complex.I / (system.hbar : ℂ)))) •
          ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s)‖ ≤
      ∑' n : ℕ, Dyson.majorant ((|lam| / system.hbar) * M) t (n + 2) := by
  have hOne : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have h := Dyson.norm_evolution_sub_one_add_term_one_le_of_bound
    (timeDependentInteractionPerturbation system V) hOne hM hV
    (timeDependentPhysicalDysonCoupling system lam) ht
  simpa only [timeDependentInteractionPropagator, timeDependentDysonTerm_one,
    norm_timeDependentPhysicalDysonCoupling] using h

/-- On `|λ| / ℏ ≤ 1`, the general time-dependent propagator remainder has an explicit quadratic
bound. -/
theorem norm_timeDependentInteractionPropagator_sub_firstOrder_le_sq_mul_of_bound
    {V : ℝ → (H →L[ℂ] H)} {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) (lam : ℝ)
    (hlam : |lam| / system.hbar ≤ 1) :
    ‖timeDependentInteractionPropagator system V lam t -
        (1 + ((lam : ℂ) * (-(Complex.I / (system.hbar : ℂ)))) •
          ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation system V s)‖ ≤
      (|lam| / system.hbar) ^ 2 *
        ∑' n : ℕ, Dyson.majorant M t (n + 2) := by
  have hOne : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have h := Dyson.norm_evolution_sub_one_add_term_one_le_sq_mul_of_bound
    (timeDependentInteractionPerturbation system V) hOne hM hV
    (timeDependentPhysicalDysonCoupling system lam)
    (by simpa [norm_timeDependentPhysicalDysonCoupling] using hlam) ht
  simpa only [timeDependentInteractionPropagator, timeDependentDysonTerm_one,
    norm_timeDependentPhysicalDysonCoupling] using h

/-- The general interaction-picture propagator is differentiable at zero physical coupling. -/
theorem hasDerivAt_timeDependentInteractionPropagator_zero_of_bound
    {V : ℝ → (H →L[ℂ] H)} {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => timeDependentInteractionPropagator system V lam t)
      (timeDependentPropagatorFirstVariation system V t)
      0 := by
  have hOne : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  simpa [timeDependentInteractionPropagator, timeDependentPhysicalDysonCoupling,
    timeDependentPropagatorFirstVariation] using
    Dyson.hasDerivAt_evolution_linear_coupling_zero_of_bound
      (timeDependentInteractionPerturbation system V) hOne hM hV ht
      (Complex.I / (system.hbar : ℂ))

end
end LinearResponse
end QuantumTheory