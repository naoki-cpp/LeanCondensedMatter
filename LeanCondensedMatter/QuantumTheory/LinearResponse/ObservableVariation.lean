import LeanCondensedMatter.QuantumTheory.LinearResponse.RetardedSusceptibility

set_option linter.style.header false

/-!
# Observable variation and contact terms in bounded linear response

The general Kubo theorem differentiates the state evolution while keeping the measured observable
fixed.  For electromagnetic response the observable may itself depend on the external source.  If
`A(λ)` is the measured observable family, differentiating

```text
ω(U_I(λ,t)† A(λ)_I(t) U_I(λ,t))
```

therefore produces two contributions:

1. the usual commutator response from the perturbed state;
2. the explicit observable variation `ω(A'(0)_I(t))`.

The second term is the abstract contact term.  In a Peierls/minimal-coupling specialization it is
the term often called diamagnetic.  This module proves the decomposition before choosing a
particular current model, so downstream conductivity APIs cannot silently discard it.
-/

namespace QuantumTheory
namespace LinearResponse

open Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- Free Heisenberg evolution bundled as a continuous complex-linear map in the observable. -/
noncomputable def heisenbergEvolutionMap (t : ℝ) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip (freePropagator system t)).comp
    ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)) (freePropagator system (-t)))

@[simp]
theorem heisenbergEvolutionMap_apply (A : H →L[ℂ] H) (t : ℝ) :
    heisenbergEvolutionMap system t A = heisenbergEvolution system A t := by
  simp [heisenbergEvolutionMap, heisenbergEvolution, mul_assoc]

/-- The interaction-picture measured observable when the Schrödinger-picture observable itself
varies with the real coupling parameter. -/
noncomputable def sourceDependentPerturbedObservable
    (V : ℝ → (H →L[ℂ] H)) (A : ℝ → (H →L[ℂ] H))
    (lam t : ℝ) : H →L[ℂ] H :=
  timeDependentPerturbedObservable system V (A lam) lam t

/-- The corresponding source-dependent measured expectation. -/
noncomputable def sourceDependentPerturbedExpectation
    (expectation : NormalizedExpectation H)
    (V : ℝ → (H →L[ℂ] H)) (A : ℝ → (H →L[ℂ] H))
    (lam t : ℝ) : ℂ :=
  expectation (sourceDependentPerturbedObservable system V A lam t)

/-- A differentiable observable family remains differentiable after free Heisenberg evolution. -/
theorem hasDerivAt_heisenbergEvolution_comp
    {A : ℝ → (H →L[ℂ] H)} {A' : H →L[ℂ] H} (hA : HasDerivAt A A' 0)
    (t : ℝ) :
    HasDerivAt
      (fun lam : ℝ => heisenbergEvolution system (A lam) t)
      (heisenbergEvolution system A' t) 0 := by
  have hmap : HasFDerivAt
      (fun X : H →L[ℂ] H => heisenbergEvolutionMap system t X)
      ((heisenbergEvolutionMap system t).restrictScalars ℝ)
      (A 0) :=
    ((heisenbergEvolutionMap system t).restrictScalars ℝ).hasFDerivAt
  have hcomp := hmap.comp 0 hA.hasFDerivAt
  simpa [Function.comp_def] using hcomp.hasDerivAt

/-- First variation of a perturbed observable family.  The derivative is the ordinary state
variation plus the free evolution of the explicit observable derivative. -/
theorem hasDerivAt_sourceDependentPerturbedObservable_zero_of_bound
    {V : ℝ → (H →L[ℂ] H)} {A : ℝ → (H →L[ℂ] H)}
    {A' : H →L[ℂ] H} (hA : HasDerivAt A A' 0)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => sourceDependentPerturbedObservable system V A lam t)
      (star (timeDependentPropagatorFirstVariation system V t) *
          heisenbergEvolution system (A 0) t +
        heisenbergEvolution system (A 0) t *
          timeDependentPropagatorFirstVariation system V t +
        heisenbergEvolution system A' t)
      0 := by
  have hU : HasDerivAt
      (fun lam : ℝ => timeDependentInteractionPropagator system V lam t)
      (timeDependentPropagatorFirstVariation system V t) 0 :=
    hasDerivAt_timeDependentInteractionPropagator_zero_of_bound system hM hV ht
  have hUstar : HasDerivAt
      (fun lam : ℝ => star (timeDependentInteractionPropagator system V lam t))
      (star (timeDependentPropagatorFirstVariation system V t)) 0 := by
    simpa [Function.comp_def] using hU.star
  have hAI := hasDerivAt_heisenbergEvolution_comp system hA t
  have hprod := (hUstar.mul hAI).mul hU
  convert hprod using 1
  · rfl
  · simp
    abel

/-- Applying the ordinary expectation to the source-dependent observable variation. -/
theorem hasDerivAt_sourceDependentPerturbedExpectation_zero_of_bound
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} {A : ℝ → (H →L[ℂ] H)}
    {A' : H →L[ℂ] H} (hA : HasDerivAt A A' 0)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => sourceDependentPerturbedExpectation system expectation V A lam t)
      (expectation
        (star (timeDependentPropagatorFirstVariation system V t) *
            heisenbergEvolution system (A 0) t +
          heisenbergEvolution system (A 0) t *
            timeDependentPropagatorFirstVariation system V t +
          heisenbergEvolution system A' t))
      0 := by
  have hObs := hasDerivAt_sourceDependentPerturbedObservable_zero_of_bound
    system hA hM hV ht
  have hExpectation : HasFDerivAt
      (fun X : H →L[ℂ] H => expectation X)
      (expectation.toContinuousLinearMap.restrictScalars ℝ)
      (sourceDependentPerturbedObservable system V A 0 t) :=
    (expectation.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt
  have hcomp := hExpectation.comp 0 hObs.hasFDerivAt
  simpa [sourceDependentPerturbedExpectation, Function.comp_def] using hcomp.hasDerivAt

/-- For a Hermitian perturbation, the state contribution is a commutator and the explicit
observable derivative remains as a separate contact term. -/
theorem hasDerivAt_sourceDependentPerturbedExpectation_zero_of_bound_of_isSelfAdjoint
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    {A : ℝ → (H →L[ℂ] H)} {A' : H →L[ℂ] H}
    (hA : HasDerivAt A A' 0)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => sourceDependentPerturbedExpectation system expectation V A lam t)
      (expectation
        (heisenbergEvolution system (A 0) t *
              timeDependentPropagatorFirstVariation system V t -
            timeDependentPropagatorFirstVariation system V t *
              heisenbergEvolution system (A 0) t +
          heisenbergEvolution system A' t))
      0 := by
  have h := hasDerivAt_sourceDependentPerturbedExpectation_zero_of_bound
    system expectation hA hM hV ht
  have hK := star_timeDependentPropagatorFirstVariation_eq_neg_of_isSelfAdjoint
    system V hVself t
  simpa [hK, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

/-- General bounded Kubo formula for a source-dependent measured observable.  The response is the
usual commutator integral plus the explicit observable-variation/contact contribution. -/
theorem hasDerivAt_sourceDependentPerturbedExpectation_zero_of_bound_kubo
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    {A : ℝ → (H →L[ℂ] H)} {A' : H →L[ℂ] H}
    (hA : HasDerivAt A A' 0)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation system V) MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ => sourceDependentPerturbedExpectation system expectation V A lam t)
      (((-(Complex.I / (system.hbar : ℂ))) •
          ∫ s in (0 : ℝ)..t,
            expectation
              (heisenbergEvolution system (A 0) t *
                  timeDependentInteractionPerturbation system V s -
                timeDependentInteractionPerturbation system V s *
                  heisenbergEvolution system (A 0) t)) +
        expectation (heisenbergEvolution system A' t))
      0 := by
  have h :=
    hasDerivAt_sourceDependentPerturbedExpectation_zero_of_bound_of_isSelfAdjoint
      system expectation hVself hA hM hV ht
  have hsplit :
      expectation
          (heisenbergEvolution system (A 0) t *
                timeDependentPropagatorFirstVariation system V t -
              timeDependentPropagatorFirstVariation system V t *
                heisenbergEvolution system (A 0) t +
            heisenbergEvolution system A' t) =
        expectation
            (heisenbergEvolution system (A 0) t *
                timeDependentPropagatorFirstVariation system V t -
              timeDependentPropagatorFirstVariation system V t *
                heisenbergEvolution system (A 0) t) +
          expectation (heisenbergEvolution system A' t) := by
    exact map_add expectation.toContinuousLinearMap _ _
  rw [hsplit] at h
  rw [expectation_commutator_firstVariation_eq_integral
    system expectation V (A 0) t hInt] at h
  exact h

/-- Scalar-source specialization written as a causal retarded response plus the contact term. -/
theorem hasDerivAt_sourceDependentSourceCoupledExpectation_zero_of_bound_retarded
    (expectation : NormalizedExpectation H)
    (f : ℝ → ℝ) {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    {A : ℝ → (H →L[ℂ] H)} {A' : H →L[ℂ] H}
    (hA : HasDerivAt A A' 0)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system
        (sourceCoupledPerturbation f B) s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation system
        (sourceCoupledPerturbation f B)) MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ => sourceDependentPerturbedExpectation system expectation
        (sourceCoupledPerturbation f B) A lam t)
      ((∫ s in (0 : ℝ)..t,
          (f s : ℂ) *
            retardedSusceptibility system expectation (A 0) B t s) +
        expectation (heisenbergEvolution system A' t))
      0 := by
  have h := hasDerivAt_sourceDependentPerturbedExpectation_zero_of_bound_kubo
    system expectation (fun s => isSelfAdjoint_sourceCoupledPerturbation f hB s)
    hA hM hV ht hInt
  rw [sourceCoupled_responseIntegral_eq system expectation f B (A 0) t] at h
  rw [sourceCoupled_responseIntegral_eq_retardedSusceptibility
    system expectation f B (A 0) ht.1] at h
  exact h

end
end LinearResponse
end QuantumTheory
