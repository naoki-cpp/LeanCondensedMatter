import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.SourceCoupling
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.Channel
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Algebra.Lie.OfAssociative

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
              ⁅heisenbergEvolution (freePropagatorGroup system) t A₀,
                timeDependentInteractionPerturbation system V s⁆) +
        expectation (heisenbergEvolution (freePropagatorGroup system) t A₁))
      0 := by
  have hfixed :=
    hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound_kubo
      system expectation hVself A₀ hM hV ht hInt
  have hcontact :=
    hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound
      system expectation A₁ hM hV ht
  have hsource : HasDerivAt (fun lam : ℝ => (lam : ℂ)) 1 0 :=
    (hasDerivAt_id (x := (0 : ℝ))).ofReal_comp
  have hsum := hfixed.add (hsource.mul hcontact)
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at hsum
  simpa [affinePerturbedExpectation, timeDependentPerturbedObservable,
    heisenbergEvolution_freePropagatorGroup_apply, mul_add, add_mul] using hsum

/-- For a real-valued source profile, the affine expectation derivative is the channel's causal
response. The observable variation is the actual affine coefficient, including any source factor
specified by the caller; it is not automatically multiplied by the profile at observation time. -/
theorem ResponseChannel.hasDerivAt_affineSourceCoupledExpectation_zero_of_bound_retarded
    (channel : ResponseChannel H) (system : BoundedFreeSystem H)
    (expectation : NormalizedExpectation H)
    (f : ℝ → ℝ) (hB : IsSelfAdjoint channel.source)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system
        (sourceCoupledPerturbation f channel.source) s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation system
        (sourceCoupledPerturbation f channel.source)) MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ => affinePerturbedExpectation system expectation
        (sourceCoupledPerturbation f channel.source)
        channel.measured channel.observableVariation lam t)
      (channel.causalResponse (freePropagatorGroup system) system.hbar expectation f t) 0 := by
  have h := hasDerivAt_affinePerturbedExpectation_zero_of_bound_kubo
    system expectation (fun s => isSelfAdjoint_sourceCoupledPerturbation f hB s)
    channel.measured channel.observableVariation hM hV ht hInt
  rw [sourceCoupled_responseIntegral_eq
    system expectation f channel.source channel.measured t] at h
  rw [sourceCoupled_responseIntegral_eq_retardedSusceptibility
    (freePropagatorGroup system) system.hbar expectation f channel.source channel.measured ht.1] at h
  simpa only [ResponseChannel.causalResponse, ResponseChannel.retardedKernel,
    ResponseChannel.contactExpectation] using h

end
end LinearResponse
end QuantumTheory
