import LeanCondensedMatter.QuantumTheory.LinearResponse.RetardedSusceptibility
import Mathlib.Analysis.Complex.RealDeriv

set_option linter.style.header false

/-!
# Observable variation and contact terms in bounded linear response

The general Kubo theorem differentiates the state evolution while keeping the measured observable
fixed. For electromagnetic response the observable may itself depend on the external source. This
module exposes the first-order source dependence by the affine family

```text
A(λ) = A₀ + λ A₁.
```

Differentiating

```text
ω(U_I(λ,t)† A(λ)_I(t) U_I(λ,t))
```

produces the usual commutator response from the perturbed state plus the explicit observable
variation `ω((A₁)_I(t))`. The latter is the abstract contact term. In a Peierls/minimal-coupling
specialization it is the term often called diamagnetic.
-/

namespace QuantumTheory
namespace LinearResponse

open Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- The source-dependent measured expectation for the affine observable family
`A(λ) = A₀ + λ A₁`. -/
noncomputable def affinePerturbedExpectation
    (expectation : NormalizedExpectation H)
    (V : ℝ → (H →L[ℂ] H)) (A₀ A₁ : H →L[ℂ] H)
    (lam t : ℝ) : ℂ :=
  expectation
    (timeDependentPerturbedObservable system V (A₀ + (lam : ℂ) • A₁) lam t)

/-- General bounded Kubo formula for an affine source-dependent measured observable. The response
is the usual commutator integral plus the explicit observable-variation/contact contribution. -/
theorem hasDerivAt_affinePerturbedExpectation_zero_of_bound_kubo
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (A₀ A₁ : H →L[ℂ] H)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation system V) MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ => affinePerturbedExpectation system expectation V A₀ A₁ lam t)
      (((-(Complex.I / (system.hbar : ℂ))) •
          ∫ s in (0 : ℝ)..t,
            expectation
              (heisenbergEvolution system A₀ t *
                  timeDependentInteractionPerturbation system V s -
                timeDependentInteractionPerturbation system V s *
                  heisenbergEvolution system A₀ t)) +
        expectation (heisenbergEvolution system A₁ t))
      0 := by
  have hfixed :=
    hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound
      system expectation A₀ hM hV ht
  have hcontact :=
    hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound
      system expectation A₁ hM hV ht
  have hsource : HasDerivAt (fun lam : ℝ => (lam : ℂ)) 1 0 :=
    (hasDerivAt_id (x := (0 : ℝ))).ofReal_comp
  have hsum := hfixed.add (hsource.mul hcontact)
  have hbase :
      HasDerivAt
        (fun lam : ℝ => affinePerturbedExpectation system expectation V A₀ A₁ lam t)
        (expectation
            (star (timeDependentPropagatorFirstVariation system V t) *
                heisenbergEvolution system A₀ t +
              heisenbergEvolution system A₀ t *
                timeDependentPropagatorFirstVariation system V t) +
          expectation (heisenbergEvolution system A₁ t))
        0 := by
    rw [hasDerivAt_iff_tendsto]
    rw [hasDerivAt_iff_tendsto] at hsum
    simpa [affinePerturbedExpectation, timeDependentPerturbedObservable,
      heisenbergEvolution, mul_add, add_mul] using hsum
  have hK := star_timeDependentPropagatorFirstVariation_eq_neg_of_isSelfAdjoint
    system V hVself t
  have hself :
      HasDerivAt
        (fun lam : ℝ => affinePerturbedExpectation system expectation V A₀ A₁ lam t)
        (expectation
            (heisenbergEvolution system A₀ t *
                timeDependentPropagatorFirstVariation system V t -
              timeDependentPropagatorFirstVariation system V t *
                heisenbergEvolution system A₀ t) +
          expectation (heisenbergEvolution system A₁ t))
        0 := by
    simpa [hK, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hbase
  rw [expectation_commutator_firstVariation_eq_integral
    system expectation V A₀ t hInt] at hself
  exact hself

/-- Scalar-source specialization written as a causal retarded response plus the contact term. -/
theorem hasDerivAt_affineSourceCoupledExpectation_zero_of_bound_retarded
    (expectation : NormalizedExpectation H)
    (f : ℝ → ℝ) {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (A₀ A₁ : H →L[ℂ] H)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system
        (sourceCoupledPerturbation f B) s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation system
        (sourceCoupledPerturbation f B)) MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ => affinePerturbedExpectation system expectation
        (sourceCoupledPerturbation f B) A₀ A₁ lam t)
      ((∫ s in (0 : ℝ)..t,
          (f s : ℂ) * retardedSusceptibility system expectation A₀ B t s) +
        expectation (heisenbergEvolution system A₁ t))
      0 := by
  have h := hasDerivAt_affinePerturbedExpectation_zero_of_bound_kubo
    system expectation (fun s => isSelfAdjoint_sourceCoupledPerturbation f hB s)
    A₀ A₁ hM hV ht hInt
  rw [sourceCoupled_responseIntegral_eq system expectation f B A₀ t] at h
  rw [sourceCoupled_responseIntegral_eq_retardedSusceptibility
    system expectation f B A₀ ht.1] at h
  exact h

end
end LinearResponse
end QuantumTheory
