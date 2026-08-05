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

local instance (priority := 2000) complexAddCommGroupFromNorm : AddCommGroup ℂ :=
  Complex.instNormedAddCommGroup.toAddCommGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- First-order source dependence of a measured observable. The real source parameter is embedded
in `ℂ` before acting on the complex operator space. -/
noncomputable def affineObservableFamily
    (A₀ A₁ : H →L[ℂ] H) (lam : ℝ) : H →L[ℂ] H :=
  A₀ + (lam : ℂ) • A₁

omit [CompleteSpace H] in
@[simp]
theorem affineObservableFamily_zero (A₀ A₁ : H →L[ℂ] H) :
    affineObservableFamily A₀ A₁ 0 = A₀ := by
  simp [affineObservableFamily]

/-- The interaction-picture measured observable with affine source dependence. -/
noncomputable def affinePerturbedObservable
    (V : ℝ → (H →L[ℂ] H)) (A₀ A₁ : H →L[ℂ] H)
    (lam t : ℝ) : H →L[ℂ] H :=
  timeDependentPerturbedObservable system V (affineObservableFamily A₀ A₁ lam) lam t

/-- The corresponding source-dependent measured expectation. -/
noncomputable def affinePerturbedExpectation
    (expectation : NormalizedExpectation H)
    (V : ℝ → (H →L[ℂ] H)) (A₀ A₁ : H →L[ℂ] H)
    (lam t : ℝ) : ℂ :=
  expectation (affinePerturbedObservable system V A₀ A₁ lam t)

/-- The affine perturbed observable splits into a fixed-observable term and a source-linear term. -/
theorem affinePerturbedObservable_eq
    (V : ℝ → (H →L[ℂ] H)) (A₀ A₁ : H →L[ℂ] H)
    (lam t : ℝ) :
    affinePerturbedObservable system V A₀ A₁ lam t =
      timeDependentPerturbedObservable system V A₀ lam t +
        (lam : ℂ) • timeDependentPerturbedObservable system V A₁ lam t := by
  simp [affinePerturbedObservable, affineObservableFamily,
    timeDependentPerturbedObservable, heisenbergEvolution, mul_add, add_mul]

/-- The affine source-dependent expectation is the sum of two fixed-observable pullbacks. -/
theorem affinePerturbedExpectation_eq
    (expectation : NormalizedExpectation H)
    (V : ℝ → (H →L[ℂ] H)) (A₀ A₁ : H →L[ℂ] H)
    (lam t : ℝ) :
    affinePerturbedExpectation system expectation V A₀ A₁ lam t =
      timeDependentPerturbedExpectationFunctional system expectation V lam t A₀ +
        (lam : ℂ) * timeDependentPerturbedExpectationFunctional system expectation V lam t A₁ := by
  rw [affinePerturbedExpectation, affinePerturbedObservable_eq]
  simp

/-- First variation of the affine source-dependent measured expectation. The derivative is the
fixed-observable state variation plus free Heisenberg evolution of the explicit observable
coefficient. -/
theorem hasDerivAt_affinePerturbedExpectation_zero_of_bound
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (A₀ A₁ : H →L[ℂ] H)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => affinePerturbedExpectation system expectation V A₀ A₁ lam t)
      (expectation
          (star (timeDependentPropagatorFirstVariation system V t) *
              heisenbergEvolution system A₀ t +
            heisenbergEvolution system A₀ t *
              timeDependentPropagatorFirstVariation system V t) +
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
  have hscaled := hsource.mul hcontact
  have hsum := hfixed.add hscaled
  simpa [affinePerturbedExpectation_eq] using hsum

/-- For a Hermitian perturbation, the state contribution is a commutator and the explicit
observable coefficient remains as a separate contact term. -/
theorem hasDerivAt_affinePerturbedExpectation_zero_of_bound_of_isSelfAdjoint
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (A₀ A₁ : H →L[ℂ] H)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => affinePerturbedExpectation system expectation V A₀ A₁ lam t)
      (expectation
          (heisenbergEvolution system A₀ t *
              timeDependentPropagatorFirstVariation system V t -
            timeDependentPropagatorFirstVariation system V t *
              heisenbergEvolution system A₀ t) +
        expectation (heisenbergEvolution system A₁ t))
      0 := by
  have h := hasDerivAt_affinePerturbedExpectation_zero_of_bound
    system expectation A₀ A₁ hM hV ht
  have hK := star_timeDependentPropagatorFirstVariation_eq_neg_of_isSelfAdjoint
    system V hVself t
  simpa [hK, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

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
  have h :=
    hasDerivAt_affinePerturbedExpectation_zero_of_bound_of_isSelfAdjoint
      system expectation hVself A₀ A₁ hM hV ht
  rw [expectation_commutator_firstVariation_eq_integral
    system expectation V A₀ t hInt] at h
  exact h

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
