import LeanCondensedMatter.QuantumTheory.LinearResponse.KuboFormula

set_option linter.style.header false

/-!
# Scalar-source specialization of the bounded Kubo formula

This module specializes the general perturbation convention

`H_λ(t) = H₀ + λ V(t)`

to the standard source coupling

`V(t) = -f(t) B`,

where `f : ℝ → ℝ` is a real source and `B` is a bounded coupling observable. The interaction-picture
perturbation is proved to be

`V_I(t) = -f(t) B_I(t)`,

and the sign in the usual Kubo response follows by substitution into the already-proved general
formula, rather than by introducing a second response convention.
-/

namespace QuantumTheory
namespace LinearResponse

open Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- The source-coupled perturbation `V(t) = -f(t) B`. -/
noncomputable def sourceCoupledPerturbation
    (f : ℝ → ℝ) (B : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  (-(f t : ℂ)) • B

/-- A real scalar source preserves self-adjointness of the coupling observable pointwise. -/
theorem isSelfAdjoint_sourceCoupledPerturbation
    (f : ℝ → ℝ) {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (t : ℝ) :
    IsSelfAdjoint (sourceCoupledPerturbation f B t) := by
  rw [isSelfAdjoint_iff]
  simp [sourceCoupledPerturbation, hB.star_eq]

/-- In the interaction picture, `-f(t) B` becomes `-f(t) B_I(t)`. -/
@[simp]
theorem timeDependentInteractionPerturbation_sourceCoupledPerturbation
    (f : ℝ → ℝ) (B : H →L[ℂ] H) (t : ℝ) :
    timeDependentInteractionPerturbation system (sourceCoupledPerturbation f B) t =
      (-(f t : ℂ)) • heisenbergEvolution system B t := by
  simp [timeDependentInteractionPerturbation, sourceCoupledPerturbation,
    heisenbergEvolution, mul_assoc]

/-- Substituting `V(t) = -f(t) B` into the general response integral produces the conventional
positive `i/ℏ` prefactor. -/
theorem sourceCoupled_responseIntegral_eq
    (expectation : NormalizedExpectation H)
    (f : ℝ → ℝ) (B A : H →L[ℂ] H) (t : ℝ) :
    ((-(Complex.I / (system.hbar : ℂ))) •
      ∫ s in (0 : ℝ)..t,
        expectation
          (heisenbergEvolution system A t *
              timeDependentInteractionPerturbation system
                (sourceCoupledPerturbation f B) s -
            timeDependentInteractionPerturbation system
                (sourceCoupledPerturbation f B) s *
              heisenbergEvolution system A t)) =
      ((Complex.I / (system.hbar : ℂ)) •
        ∫ s in (0 : ℝ)..t,
          (f s : ℂ) *
            expectation
              (heisenbergEvolution system A t * heisenbergEvolution system B s -
                heisenbergEvolution system B s * heisenbergEvolution system A t)) := by
  let g : ℝ → ℂ := fun s =>
    (f s : ℂ) *
      expectation
        (heisenbergEvolution system A t * heisenbergEvolution system B s -
          heisenbergEvolution system B s * heisenbergEvolution system A t)
  have hfun :
      (fun s : ℝ =>
        expectation
          (heisenbergEvolution system A t *
              timeDependentInteractionPerturbation system
                (sourceCoupledPerturbation f B) s -
            timeDependentInteractionPerturbation system
                (sourceCoupledPerturbation f B) s *
              heisenbergEvolution system A t)) =
        fun s => -g s := by
    funext s
    rw [timeDependentInteractionPerturbation_sourceCoupledPerturbation]
    calc
      expectation
          (heisenbergEvolution system A t *
              ((-(f s : ℂ)) • heisenbergEvolution system B s) -
            ((-(f s : ℂ)) • heisenbergEvolution system B s) *
              heisenbergEvolution system A t) =
        expectation
          ((-(f s : ℂ)) •
            (heisenbergEvolution system A t * heisenbergEvolution system B s -
              heisenbergEvolution system B s * heisenbergEvolution system A t)) := by
        congr 1
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      _ = (-(f s : ℂ)) *
          expectation
            (heisenbergEvolution system A t * heisenbergEvolution system B s -
              heisenbergEvolution system B s * heisenbergEvolution system A t) := by
        exact map_smul expectation.toContinuousLinearMap _ _
      _ = -g s := by
        simp [g]
  rw [hfun, intervalIntegral.integral_neg]
  simp [g]

/-- The bounded Kubo formula for the standard source convention
`H_λ(t) = H₀ - λ f(t) B`. -/
theorem hasDerivAt_sourceCoupledPerturbedExpectation_zero_of_bound_kubo
    (expectation : NormalizedExpectation H)
    (f : ℝ → ℝ) {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (A : H →L[ℂ] H) {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system
        (sourceCoupledPerturbation f B) s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation system
        (sourceCoupledPerturbation f B)) MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ =>
        timeDependentPerturbedExpectationFunctional system expectation
          (sourceCoupledPerturbation f B) lam t A)
      ((Complex.I / (system.hbar : ℂ)) •
        ∫ s in (0 : ℝ)..t,
          (f s : ℂ) *
            expectation
              (heisenbergEvolution system A t * heisenbergEvolution system B s -
                heisenbergEvolution system B s * heisenbergEvolution system A t))
      0 := by
  have hgeneral :=
    hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound_kubo
      system expectation
        (fun s => isSelfAdjoint_sourceCoupledPerturbation f hB s)
        A hM hV ht hInt
  rw [sourceCoupled_responseIntegral_eq system expectation f B A t] at hgeneral
  exact hgeneral

/-- Density-operator specialization of the scalar-source Kubo formula. -/
theorem hasDerivAt_densityOperatorSourceCoupledExpectation_zero_of_bound_kubo
    (ρ : DensityOperator H)
    (f : ℝ → ℝ) {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (A : H →L[ℂ] H) {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system
        (sourceCoupledPerturbation f B) s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation system
        (sourceCoupledPerturbation f B)) MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ => ρ.expectation
        (timeDependentPerturbedObservable system
          (sourceCoupledPerturbation f B) A lam t))
      ((Complex.I / (system.hbar : ℂ)) •
        ∫ s in (0 : ℝ)..t,
          (f s : ℂ) *
            ρ.expectation
              (heisenbergEvolution system A t * heisenbergEvolution system B s -
                heisenbergEvolution system B s * heisenbergEvolution system A t))
      0 := by
  simpa using
    (hasDerivAt_sourceCoupledPerturbedExpectation_zero_of_bound_kubo
      system ρ.toNormalizedExpectation f hB A hM hV ht hInt)

end
end LinearResponse
end QuantumTheory
