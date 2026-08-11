import LeanCondensedMatter.QuantumTheory.LinearResponse.DensityExpectation
import LeanCondensedMatter.QuantumTheory.LinearResponse.HermitianPerturbation
import LeanCondensedMatter.QuantumTheory.LinearResponse.Stationarity
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Operator.Mul

set_option linter.style.header false

/-!
# General Kubo expectation formula

For the bounded time-dependent perturbation convention

`H_λ(t) = H₀ + λ V(t)`,

this module derives the perturbed expectation from an ordinary normalized expectation `ω`. The
interaction-picture observable evolution defines the pullback functional

`ω_{λ,t}(A) = ω(U_{I,λ}(t)† A_I(t) U_{I,λ}(t))`.

At zero coupling this is the ordinary expectation composed with free Heisenberg evolution, and it
reduces to `ω(A)` whenever `ω` is stationary.

For a pointwise self-adjoint perturbation, the derivative at zero coupling is

`ω([A_I(t), K_V(t)])`,

where

`K_V(t) = -(i / ℏ) ∫₀ᵗ V_I(s) ds`.

When `V_I` is interval-integrable, continuity and linearity of `ω` give the general Kubo formula

`-(i / ℏ) ∫₀ᵗ ω([A_I(t), V_I(s)]) ds`.

The finite-coupling pullback is kept as a continuous linear functional rather than bundled as a
`NormalizedExpectation`: normalization would require full unitarity of the Dyson propagator, which
is a separate theorem.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- The interaction-picture observable conjugated by the perturbed propagator. -/
noncomputable def timeDependentPerturbedObservable
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H)
    (lam t : ℝ) : H →L[ℂ] H :=
  star (timeDependentInteractionPropagator system V lam t) *
    heisenbergEvolution system A t *
      timeDependentInteractionPropagator system V lam t

/-- The continuous linear map sending an ordinary observable `A` to its perturbed
interaction-picture representative `U_I† A_I U_I`. -/
noncomputable def timeDependentPerturbedObservableMap
    (V : ℝ → (H →L[ℂ] H)) (lam t : ℝ) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  let U := timeDependentInteractionPropagator system V lam t
  let left := star U * freePropagator system (-t)
  let right := freePropagator system t * U
  ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip right).comp
    ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)) left)

@[simp]
theorem timeDependentPerturbedObservableMap_apply
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H)
    (lam t : ℝ) :
    timeDependentPerturbedObservableMap system V lam t A =
      timeDependentPerturbedObservable system V A lam t := by
  simp [timeDependentPerturbedObservableMap, timeDependentPerturbedObservable,
    heisenbergEvolution, mul_assoc]

/-- The perturbed expectation functional derived from the ordinary expectation by pullback along
`A ↦ U_I† A_I U_I`. -/
noncomputable def timeDependentPerturbedExpectationFunctional
    (expectation : NormalizedExpectation H)
    (V : ℝ → (H →L[ℂ] H)) (lam t : ℝ) :
    (H →L[ℂ] H) →L[ℂ] ℂ :=
  expectation.toContinuousLinearMap.comp
    (timeDependentPerturbedObservableMap system V lam t)

@[simp]
theorem timeDependentPerturbedExpectationFunctional_apply
    (expectation : NormalizedExpectation H)
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H)
    (lam t : ℝ) :
    timeDependentPerturbedExpectationFunctional system expectation V lam t A =
      expectation (timeDependentPerturbedObservable system V A lam t) := by
  simp [timeDependentPerturbedExpectationFunctional]

@[simp]
theorem timeDependentPerturbedObservable_zero_coupling
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H) (t : ℝ) :
    timeDependentPerturbedObservable system V A 0 t =
      heisenbergEvolution system A t := by
  simp [timeDependentPerturbedObservable]

/-- At zero coupling, the perturbed functional is the ordinary expectation composed with free
Heisenberg evolution. -/
theorem timeDependentPerturbedExpectationFunctional_zero_coupling_apply
    (expectation : NormalizedExpectation H)
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H) (t : ℝ) :
    timeDependentPerturbedExpectationFunctional system expectation V 0 t A =
      expectation (heisenbergEvolution system A t) := by
  simp

/-- For a stationary ordinary expectation, the zero-coupling pullback is exactly the original
expectation. -/
theorem timeDependentPerturbedExpectationFunctional_zero_coupling_apply_of_stationary
    (expectation : NormalizedExpectation H)
    (hstationary : IsStationary system expectation)
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H) (t : ℝ) :
    timeDependentPerturbedExpectationFunctional system expectation V 0 t A =
      expectation A := by
  simpa using hstationary t A

/-- The first variation of `U† A_I U` before imposing Hermiticity of the perturbation. -/
theorem hasDerivAt_timeDependentPerturbedObservable_zero_of_bound
    {V : ℝ → (H →L[ℂ] H)} (A : H →L[ℂ] H)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => timeDependentPerturbedObservable system V A lam t)
      (star (timeDependentPropagatorFirstVariation system V t) *
          heisenbergEvolution system A t +
        heisenbergEvolution system A t *
          timeDependentPropagatorFirstVariation system V t)
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
  have hleft := hUstar.mul_const (heisenbergEvolution system A t)
  have hprod := hleft.mul hU
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at hprod
  simpa [timeDependentPerturbedObservable, mul_assoc] using hprod

/-- Applying the ordinary expectation to the observable first variation gives the derivative of the
pulled-back perturbed expectation. -/
theorem hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (A : H →L[ℂ] H)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ =>
        timeDependentPerturbedExpectationFunctional system expectation V lam t A)
      (expectation
        (star (timeDependentPropagatorFirstVariation system V t) *
            heisenbergEvolution system A t +
          heisenbergEvolution system A t *
            timeDependentPropagatorFirstVariation system V t))
      0 := by
  have hObs := hasDerivAt_timeDependentPerturbedObservable_zero_of_bound
    system A hM hV ht
  have hExpectation : HasFDerivAt
      (fun X : H →L[ℂ] H => expectation X)
      (expectation.toContinuousLinearMap.restrictScalars ℝ)
      (timeDependentPerturbedObservable system V A 0 t) :=
    (expectation.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt
  have hcomp := hExpectation.comp 0 hObs.hasFDerivAt
  have hderiv := hcomp.hasDerivAt
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at hderiv
  simpa [timeDependentPerturbedExpectationFunctional_apply, Function.comp_def] using hderiv

/-- For a Hermitian perturbation, the expectation first variation is the ordinary expectation of
`[A_I(t), K_V(t)]`. -/
theorem hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound_of_isSelfAdjoint
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (A : H →L[ℂ] H) {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ =>
        timeDependentPerturbedExpectationFunctional system expectation V lam t A)
      (expectation
        (heisenbergEvolution system A t *
            timeDependentPropagatorFirstVariation system V t -
          timeDependentPropagatorFirstVariation system V t *
            heisenbergEvolution system A t))
      0 := by
  have h :=
    hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound
      system expectation A hM hV ht
  have hK := star_timeDependentPropagatorFirstVariation_eq_neg_of_isSelfAdjoint
    system V hVself t
  simpa [hK, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

/-- The continuous linear functional `X ↦ ω(A X - X A)`. -/
noncomputable def commutatorExpectation
    (expectation : NormalizedExpectation H) (A : H →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] ℂ :=
  expectation.toContinuousLinearMap.comp
    (((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)) A) -
      ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip A))

@[simp]
theorem commutatorExpectation_apply
    (expectation : NormalizedExpectation H)
    (A X : H →L[ℂ] H) :
    commutatorExpectation expectation A X =
      expectation (A * X - X * A) := by
  simp [commutatorExpectation]

/-- The commutator with the first propagator variation is the interval integral of the
instantaneous commutator response. -/
theorem expectation_commutator_firstVariation_eq_integral
    (expectation : NormalizedExpectation H)
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H) (t : ℝ)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation system V) MeasureTheory.volume 0 t) :
    expectation
        (heisenbergEvolution system A t *
            timeDependentPropagatorFirstVariation system V t -
          timeDependentPropagatorFirstVariation system V t *
            heisenbergEvolution system A t) =
      (-(Complex.I / (system.hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          expectation
            (heisenbergEvolution system A t *
                timeDependentInteractionPerturbation system V s -
              timeDependentInteractionPerturbation system V s *
                heisenbergEvolution system A t) := by
  let L := commutatorExpectation expectation (heisenbergEvolution system A t)
  have hmap := ContinuousLinearMap.intervalIntegral_comp_comm L hInt
  calc
    expectation
        (heisenbergEvolution system A t *
            timeDependentPropagatorFirstVariation system V t -
          timeDependentPropagatorFirstVariation system V t *
            heisenbergEvolution system A t) =
        L (timeDependentPropagatorFirstVariation system V t) := by
      simp [L]
    _ = L ((-(Complex.I / (system.hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          timeDependentInteractionPerturbation system V s) := by
      rfl
    _ = (-(Complex.I / (system.hbar : ℂ))) •
        L (∫ s in (0 : ℝ)..t,
          timeDependentInteractionPerturbation system V s) := by
      rw [map_smul]
    _ = (-(Complex.I / (system.hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          L (timeDependentInteractionPerturbation system V s) := by
      rw [hmap]
    _ = (-(Complex.I / (system.hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          expectation
            (heisenbergEvolution system A t *
                timeDependentInteractionPerturbation system V s -
              timeDependentInteractionPerturbation system V s *
                heisenbergEvolution system A t) := by
      simp [L]

/-- The general bounded Kubo formula for the pullback of an ordinary expectation by a pointwise
Hermitian, interval-integrable perturbation. -/
theorem hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound_kubo
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (A : H →L[ℂ] H) {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation system V) MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ =>
        timeDependentPerturbedExpectationFunctional system expectation V lam t A)
      ((-(Complex.I / (system.hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          expectation
            (heisenbergEvolution system A t *
                timeDependentInteractionPerturbation system V s -
              timeDependentInteractionPerturbation system V s *
                heisenbergEvolution system A t))
      0 := by
  have h :=
    hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound_of_isSelfAdjoint
      system expectation hVself A hM hV ht
  rw [expectation_commutator_firstVariation_eq_integral
    system expectation V A t hInt] at h
  exact h

/-- Density-operator specialization of the general bounded Kubo formula. -/
theorem hasDerivAt_densityOperatorExpectation_zero_of_bound_kubo
    (ρ : DensityOperator H)
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (A : H →L[ℂ] H) {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation system V) MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ => ρ.expectation
        (timeDependentPerturbedObservable system V A lam t))
      ((-(Complex.I / (system.hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          ρ.expectation
            (heisenbergEvolution system A t *
                timeDependentInteractionPerturbation system V s -
              timeDependentInteractionPerturbation system V s *
                heisenbergEvolution system A t))
      0 := by
  simpa using
    (hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound_kubo
      system ρ.toNormalizedExpectation hVself A hM hV ht hInt)

end
end LinearResponse
end QuantumTheory
