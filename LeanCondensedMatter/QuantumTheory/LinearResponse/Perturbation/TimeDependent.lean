import LeanCondensedMatter.Analysis.Dyson.FirstVariation
import LeanCondensedMatter.Analysis.Dyson.Volterra
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Unitary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option linter.style.header false

/-!
# General bounded time-dependent perturbations

This module owns the bounded interaction-picture time evolution for a general time-dependent
perturbation

`H_λ(t) = H₀ + λ V(t)`

without assuming a separated source form such as `f(t) B`. Its interaction-picture representative is

`V_I(t) = U₀(-t) V(t) U₀(t)`.

The generic Dyson recursion uses `Dₙ₊₁(t) = -∫₀ᵗ V_I(s) Dₙ(s) ds`, so the physical scalar coupling
is `λ i / ℏ`. Consequently the propagator solves the corresponding Volterra equation and its first
variation is

`K_V(t) = -(i / ℏ) ∫₀ᵗ V_I(s) ds`.

Source-coupled perturbations are downstream specializations obtained by choosing, for example,
`V(t) = -f(t) B`.

The unperturbed dynamics are supplied as a one-parameter unitary group, without assuming a bounded
generator. All perturbations are bounded operators. Continuity, interval integrability, and compact
interval norm bounds on `V_I` are explicit at the theorems that use them. Physical applications
supply positive `hbar` and consistently scaled propagators; the algebraic definitions also allow
other real parameters, and scalar norm estimates therefore use `|hbar|`.
The Dyson construction is in the interaction picture. Identifying the full propagator with an
unbounded Schrödinger generator `H₀ + λ V(t)` requires separate domain and evolution arguments.
-/

namespace QuantumTheory
namespace LinearResponse

open Filter Set
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)

/-- The interaction-picture form `V_I(t) = U₀(-t) V(t) U₀(t)` of a general time-dependent
bounded perturbation. -/
noncomputable def timeDependentInteractionPerturbation
    (V : ℝ → (H →L[ℂ] H)) (t : ℝ) : H →L[ℂ] H :=
  heisenbergEvolution U t (V t)

/-- The generic Dyson scalar corresponding to `H_λ(t) = H₀ + λ V(t)`. -/
noncomputable def timeDependentPhysicalDysonCoupling (lam : ℝ) : ℂ :=
  (lam : ℂ) * (Complex.I / (hbar : ℂ))

/-- The norm of the scalar coupling is `|λ| / |ℏ|`, agreeing with `|λ| / ℏ` for positive ℏ. -/
theorem norm_timeDependentPhysicalDysonCoupling (lam : ℝ) :
    ‖timeDependentPhysicalDysonCoupling hbar lam‖ = |lam| / |hbar| := by
  simp [timeDependentPhysicalDysonCoupling, div_eq_mul_inv]

/-- The interaction-picture propagator for the general perturbation `H₀ + λ V(t)`. -/
noncomputable def timeDependentInteractionPropagator
    (V : ℝ → (H →L[ℂ] H)) (lam t : ℝ) : H →L[ℂ] H :=
  Dyson.evolution (timeDependentInteractionPerturbation U V)
    (timeDependentPhysicalDysonCoupling hbar lam) t

/-- The first propagator variation
`K_V(t) = -(i / ℏ) ∫₀ᵗ V_I(s) ds`. -/
noncomputable def timeDependentPropagatorFirstVariation
    (V : ℝ → (H →L[ℂ] H)) (t : ℝ) : H →L[ℂ] H :=
  (-(Complex.I / (hbar : ℂ))) •
    ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation U V s

private theorem timeDependentDysonBoundedInteraction
    {V : ℝ → (H →L[ℂ] H)} {β M : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M) :
    Dyson.BoundedInteraction (timeDependentInteractionPerturbation U V) β M := by
  exact
    { norm_one_le := by
        change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
        exact ContinuousLinearMap.norm_id_le
      bound_nonneg := hM
      interaction_norm_le := hV }

@[simp]
theorem timeDependentInteractionPropagator_zero_coupling
    (V : ℝ → (H →L[ℂ] H)) (t : ℝ) :
    timeDependentInteractionPropagator U hbar V 0 t = 1 := by
  simpa [timeDependentInteractionPropagator, timeDependentPhysicalDysonCoupling] using
    Dyson.evolution_zero_coupling (timeDependentInteractionPerturbation U V) t

@[simp]
theorem timeDependentInteractionPropagator_zero_time
    (V : ℝ → (H →L[ℂ] H)) (lam : ℝ) :
    timeDependentInteractionPropagator U hbar V lam 0 = 1 := by
  simp [timeDependentInteractionPropagator]

/-- Under explicit continuity and uniform boundedness hypotheses, the general interaction-picture
propagator satisfies the Volterra equation with the sign dictated by `H_λ(t) = H₀ + λ V(t)`. -/
theorem timeDependentInteractionPropagator_eq_one_sub_integral_of_bound
    {V : ℝ → (H →L[ℂ] H)}
    (hVcont : Continuous (timeDependentInteractionPerturbation U V))
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) (lam : ℝ) :
    timeDependentInteractionPropagator U hbar V lam t =
      1 - ((lam : ℂ) * (Complex.I / (hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          timeDependentInteractionPerturbation U V s *
            timeDependentInteractionPropagator U hbar V lam s := by
  have hDyson : Dyson.ContinuousBoundedInteraction
      (timeDependentInteractionPerturbation U V) β M := by
    exact
      { toBoundedInteraction := timeDependentDysonBoundedInteraction U hM hV
        interaction_continuous := hVcont }
  simpa [timeDependentInteractionPropagator, timeDependentPhysicalDysonCoupling] using
    (Dyson.evolution_eq_one_sub_integral_of_bound
      hDyson ht (timeDependentPhysicalDysonCoupling hbar lam))

/-- The exact first weighted Dyson term for `H₀ + λ V(t)`. -/
private theorem timeDependentDysonTerm_one
    (V : ℝ → (H →L[ℂ] H)) (lam t : ℝ) :
    Dyson.term (timeDependentInteractionPerturbation U V)
        (timeDependentPhysicalDysonCoupling hbar lam) t 1 =
      ((lam : ℂ) * (-(Complex.I / (hbar : ℂ)))) •
        ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation U V s := by
  rw [Dyson.term_one]
  congr 1
  simp [timeDependentPhysicalDysonCoupling]

/-- After subtracting the identity and exact first term, the propagator remainder starts at order
`λ²`. -/
theorem norm_timeDependentInteractionPropagator_sub_firstOrder_le_of_bound
    {V : ℝ → (H →L[ℂ] H)} {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) (lam : ℝ) :
    ‖timeDependentInteractionPropagator U hbar V lam t -
        (1 + ((lam : ℂ) * (-(Complex.I / (hbar : ℂ)))) •
          ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation U V s)‖ ≤
      ∑' n : ℕ, Dyson.majorant ((|lam| / |hbar|) * M) t (n + 2) := by
  have h := Dyson.norm_evolution_sub_one_add_term_one_le_of_bound
    (timeDependentDysonBoundedInteraction U hM hV)
    (timeDependentPhysicalDysonCoupling hbar lam) ht
  simpa only [timeDependentInteractionPropagator, timeDependentDysonTerm_one,
    norm_timeDependentPhysicalDysonCoupling] using h

/-- On `|λ| / |ℏ| ≤ 1`, the general time-dependent propagator remainder has an explicit quadratic
bound. -/
theorem norm_timeDependentInteractionPropagator_sub_firstOrder_le_sq_mul_of_bound
    {V : ℝ → (H →L[ℂ] H)} {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) (lam : ℝ)
    (hlam : |lam| / |hbar| ≤ 1) :
    ‖timeDependentInteractionPropagator U hbar V lam t -
        (1 + ((lam : ℂ) * (-(Complex.I / (hbar : ℂ)))) •
          ∫ s in (0 : ℝ)..t, timeDependentInteractionPerturbation U V s)‖ ≤
      (|lam| / |hbar|) ^ 2 *
        ∑' n : ℕ, Dyson.majorant M t (n + 2) := by
  have h := Dyson.norm_evolution_sub_one_add_term_one_le_sq_mul_of_bound
    (timeDependentDysonBoundedInteraction U hM hV)
    (timeDependentPhysicalDysonCoupling hbar lam)
    (by simpa [norm_timeDependentPhysicalDysonCoupling] using hlam) ht
  simpa only [timeDependentInteractionPropagator, timeDependentDysonTerm_one,
    norm_timeDependentPhysicalDysonCoupling] using h

/-- The general interaction-picture propagator is differentiable at zero physical coupling. -/
theorem hasDerivAt_timeDependentInteractionPropagator_zero_of_bound
    {V : ℝ → (H →L[ℂ] H)} {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => timeDependentInteractionPropagator U hbar V lam t)
      (timeDependentPropagatorFirstVariation U hbar V t)
      0 := by
  simpa [timeDependentInteractionPropagator, timeDependentPhysicalDysonCoupling,
    timeDependentPropagatorFirstVariation] using
    Dyson.hasDerivAt_evolution_linear_coupling_zero_of_bound
      (timeDependentDysonBoundedInteraction U hM hV) ht
      (Complex.I / (hbar : ℂ))

end
end LinearResponse
end QuantumTheory
