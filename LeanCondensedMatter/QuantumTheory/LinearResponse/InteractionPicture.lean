import LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics

set_option linter.style.header false

/-!
# Interaction-picture bounded perturbations

For the perturbation convention

`H_λ(t) = H₀ - λ f(t) B`,

the interaction-picture perturbation is `V_I(t) = f(t) B_I(t)`. Since the generic Dyson owner uses

`U(t) = 1 - α ∫₀ᵗ V_I(s) U(s) ds`,

the physical coupling supplied to it is

`α(λ) = -λ i / ℏ`.

Consequently the physical Volterra equation contains `+ λ i / ℏ`, derived from the Hamiltonian
sign rather than inserted after the fact. This module records that translation and the exact first
Dyson term. Differentiability in `λ` and the observable commutator response are added in later
modules.
-/

namespace QuantumTheory
namespace LinearResponse

open Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- The interaction-picture perturbation `V_I(t) = f(t) B_I(t)`. -/
noncomputable def interactionPerturbation (B : H →L[ℂ] H) (f : ℝ → ℝ) (t : ℝ) :
    H →L[ℂ] H :=
  (f t : ℂ) • heisenbergEvolution system B t

/-- The generic Dyson coupling corresponding to `H_λ(t) = H₀ - λ f(t) B`. -/
noncomputable def physicalDysonCoupling (lam : ℝ) : ℂ :=
  -((lam : ℂ) * (Complex.I / (system.hbar : ℂ)))

@[simp]
theorem physicalDysonCoupling_zero : physicalDysonCoupling system 0 = 0 := by
  simp [physicalDysonCoupling]

/-- The interaction-picture propagator obtained from the generic bounded Dyson evolution. -/
noncomputable def interactionPropagator (B : H →L[ℂ] H) (f : ℝ → ℝ)
    (lam t : ℝ) : H →L[ℂ] H :=
  Dyson.evolution (interactionPerturbation system B f) (physicalDysonCoupling system lam) t

@[simp]
theorem interactionPerturbation_zero_source (B : H →L[ℂ] H) (t : ℝ) :
    interactionPerturbation system B (fun _ => 0) t = 0 := by
  simp [interactionPerturbation]

omit [CompleteSpace H] in
/-- A generic Dyson evolution is the identity at zero coupling. -/
theorem dysonEvolution_zero_coupling (V : ℝ → (H →L[ℂ] H)) (t : ℝ) :
    Dyson.evolution V 0 t = 1 := by
  rw [Dyson.evolution, tsum_eq_single 0]
  · simp [Dyson.term]
  · intro n hn
    simp [Dyson.term, hn]

@[simp]
theorem interactionPropagator_zero_coupling (B : H →L[ℂ] H) (f : ℝ → ℝ) (t : ℝ) :
    interactionPropagator system B f 0 t = 1 := by
  simp [interactionPropagator, dysonEvolution_zero_coupling]

@[simp]
theorem interactionPropagator_zero_time (B : H →L[ℂ] H) (f : ℝ → ℝ) (lam : ℝ) :
    interactionPropagator system B f lam 0 = 1 := by
  simp [interactionPropagator]

omit [CompleteSpace H] in
/-- The first generic Dyson coefficient is the negative integral of the interaction. -/
theorem dysonCoeff_one (V : ℝ → (H →L[ℂ] H)) (t : ℝ) :
    Dyson.coeff V 1 t = -∫ s in (0 : ℝ)..t, V s := by
  rw [show (1 : ℕ) = 0 + 1 by rfl, Dyson.coeff_succ]
  simp

/-- The first weighted Dyson term for `H_λ = H₀ - λ f B` has coefficient `+iλ/ℏ`. -/
theorem interactionDysonTerm_one (B : H →L[ℂ] H) (f : ℝ → ℝ)
    (lam t : ℝ) :
    Dyson.term (interactionPerturbation system B f) (physicalDysonCoupling system lam) t 1 =
      ((lam : ℂ) * (Complex.I / (system.hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t, interactionPerturbation system B f s := by
  simp [Dyson.term, physicalDysonCoupling, dysonCoeff_one]

/-- Under explicit continuity and uniform boundedness hypotheses, the physical interaction-picture
propagator satisfies the Volterra equation with the sign dictated by
`H_λ(t) = H₀ - λ f(t) B`. -/
theorem interactionPropagator_eq_one_add_integral_of_bound
    {B : H →L[ℂ] H} {f : ℝ → ℝ}
    (hVcont : Continuous (interactionPerturbation system B f))
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β, ‖interactionPerturbation system B f s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) (lam : ℝ) :
    interactionPropagator system B f lam t =
      1 + ((lam : ℂ) * (Complex.I / (system.hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          interactionPerturbation system B f s * interactionPropagator system B f lam s := by
  have h := BoundedDyson.evolution_eq_one_sub_integral_of_bound
    hVcont hM hV ht (physicalDysonCoupling system lam)
  simpa [interactionPropagator, physicalDysonCoupling, sub_eq_add_neg] using h

end
end LinearResponse
end QuantumTheory
