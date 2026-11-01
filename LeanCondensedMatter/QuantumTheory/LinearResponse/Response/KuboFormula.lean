import LeanCondensedMatter.Analysis.Operator.AdjointConjugation
import LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation.Density
import LeanCondensedMatter.QuantumTheory.LinearResponse.Perturbation.Hermitian
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Stationarity
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Algebra.Lie.OfAssociative

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

The linear-response principle used here is due to Kubo, *J. Phys. Soc. Jpn.* **12**, 570–586
(1957), [doi:10.1143/JPSJ.12.570](https://doi.org/10.1143/JPSJ.12.570). The bounded-perturbation,
finite-time hypotheses are this library's explicit specialization. The unperturbed dynamics are
an arbitrary supplied unitary group; the generator need not be bounded. The derivative is with
respect to coupling at fixed observation time, not an operator-norm time derivative of that group.

The finite-coupling pullback is kept as a continuous linear functional rather than bundled as a
`NormalizedExpectation`: normalization would require full unitarity of the Dyson propagator, which
is a separate theorem.

For Stone dynamics, these theorems evaluate the defined interaction-picture Dyson perturbation
under their explicit norm-bound and integrability hypotheses. They do not identify its full
Schrödinger-picture evolution with the Stone evolution of a perturbed unbounded generator.
-/

namespace QuantumTheory
namespace LinearResponse

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)

/-- The interaction-picture observable conjugated by the perturbed propagator. -/
noncomputable def timeDependentPerturbedObservable
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H)
    (lam t : ℝ) : H →L[ℂ] H :=
  ContinuousLinearMap.adjointConjugate
    (star (timeDependentInteractionPropagator U hbar V lam t))
    (heisenbergEvolution U t A)

/-- The continuous linear map sending an ordinary observable `A` to its perturbed
interaction-picture representative `U_I† A_I U_I`. -/
noncomputable def timeDependentPerturbedObservableMap
    (V : ℝ → (H →L[ℂ] H)) (lam t : ℝ) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  let W := timeDependentInteractionPropagator U hbar V lam t
  let U₀ : H →L[ℂ] H := U (Multiplicative.ofAdd t)
  let left := star W * star U₀
  let right := U₀ * W
  ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip right).comp
    ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)) left)

@[simp]
theorem timeDependentPerturbedObservableMap_apply
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H)
    (lam t : ℝ) :
    timeDependentPerturbedObservableMap U hbar V lam t A =
      timeDependentPerturbedObservable U hbar V A lam t := by
  simp [timeDependentPerturbedObservableMap, timeDependentPerturbedObservable,
    ContinuousLinearMap.adjointConjugate, heisenbergEvolution_apply, mul_assoc]

/-- The perturbed expectation functional derived from the ordinary expectation by pullback along
`A ↦ U_I† A_I U_I`. -/
noncomputable def timeDependentPerturbedExpectationFunctional
    (expectation : NormalizedExpectation H)
    (V : ℝ → (H →L[ℂ] H)) (lam t : ℝ) :
    (H →L[ℂ] H) →L[ℂ] ℂ :=
  expectation.toContinuousLinearMap.comp
    (timeDependentPerturbedObservableMap U hbar V lam t)

@[simp]
theorem timeDependentPerturbedExpectationFunctional_apply
    (expectation : NormalizedExpectation H)
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H)
    (lam t : ℝ) :
    timeDependentPerturbedExpectationFunctional U hbar expectation V lam t A =
      expectation (timeDependentPerturbedObservable U hbar V A lam t) := by
  simp [timeDependentPerturbedExpectationFunctional]

@[simp]
theorem timeDependentPerturbedObservable_zero_coupling
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H) (t : ℝ) :
    timeDependentPerturbedObservable U hbar V A 0 t =
      heisenbergEvolution U t A := by
  simp [timeDependentPerturbedObservable, ContinuousLinearMap.adjointConjugate]

/-- At zero coupling, the perturbed functional is the ordinary expectation composed with free
Heisenberg evolution. -/
theorem timeDependentPerturbedExpectationFunctional_zero_coupling_apply
    (expectation : NormalizedExpectation H)
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H) (t : ℝ) :
    timeDependentPerturbedExpectationFunctional U hbar expectation V 0 t A =
      expectation (heisenbergEvolution U t A) := by
  simp

/-- For a stationary ordinary expectation, the zero-coupling pullback is exactly the original
expectation. -/
theorem timeDependentPerturbedExpectationFunctional_zero_coupling_apply_of_stationary
    (expectation : NormalizedExpectation H)
    (hstationary : IsStationary U expectation)
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H) (t : ℝ) :
    timeDependentPerturbedExpectationFunctional U hbar expectation V 0 t A =
      expectation A := by
  simpa using hstationary t A

/-- The first variation of `U† A_I U` before imposing Hermiticity of the perturbation. -/
theorem hasDerivAt_timeDependentPerturbedObservable_zero_of_bound
    {V : ℝ → (H →L[ℂ] H)} (A : H →L[ℂ] H)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ => timeDependentPerturbedObservable U hbar V A lam t)
      (star (timeDependentPropagatorFirstVariation U hbar V t) *
          heisenbergEvolution U t A +
        heisenbergEvolution U t A *
          timeDependentPropagatorFirstVariation U hbar V t)
      0 := by
  have hU : HasDerivAt
      (fun lam : ℝ => timeDependentInteractionPropagator U hbar V lam t)
      (timeDependentPropagatorFirstVariation U hbar V t)
      0 :=
    hasDerivAt_timeDependentInteractionPropagator_zero_of_bound U hbar hM hV ht
  simpa [timeDependentPerturbedObservable, ContinuousLinearMap.adjointConjugate] using
    ContinuousLinearMap.hasDerivAt_adjointConjugate hU.star
      (heisenbergEvolution U t A)

/-- Applying the ordinary expectation to the observable first variation gives the derivative of the
pulled-back perturbed expectation. -/
theorem hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (A : H →L[ℂ] H)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ =>
        timeDependentPerturbedExpectationFunctional U hbar expectation V lam t A)
      (expectation
        (star (timeDependentPropagatorFirstVariation U hbar V t) *
            heisenbergEvolution U t A +
          heisenbergEvolution U t A *
            timeDependentPropagatorFirstVariation U hbar V t))
      0 := by
  have hObs := hasDerivAt_timeDependentPerturbedObservable_zero_of_bound
    U hbar A hM hV ht
  have hExpectation : HasFDerivAt
      (fun X : H →L[ℂ] H => expectation X)
      (expectation.toContinuousLinearMap.restrictScalars ℝ)
      (timeDependentPerturbedObservable U hbar V A 0 t) :=
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
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    HasDerivAt
      (fun lam : ℝ =>
        timeDependentPerturbedExpectationFunctional U hbar expectation V lam t A)
      (expectation
        ⁅heisenbergEvolution U t A,
          timeDependentPropagatorFirstVariation U hbar V t⁆)
      0 := by
  have h :=
    hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound
      U hbar expectation A hM hV ht
  have hK := star_timeDependentPropagatorFirstVariation_eq_neg_of_isSelfAdjoint
    U hbar V hVself t
  simpa [LieRing.of_associative_ring_bracket, hK, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using h

/-- The continuous linear functional `X ↦ ω(A X - X A)`. -/
private noncomputable def commutatorExpectation
    (expectation : NormalizedExpectation H) (A : H →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] ℂ :=
  expectation.toContinuousLinearMap.comp
    (((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)) A) -
      ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip A))

private theorem commutatorExpectation_apply
    (expectation : NormalizedExpectation H)
    (A X : H →L[ℂ] H) :
    commutatorExpectation expectation A X =
      expectation ⁅A, X⁆ := by
  simp [commutatorExpectation, LieRing.of_associative_ring_bracket]

/-- The commutator with the first propagator variation is the interval integral of the
instantaneous commutator response. -/
theorem expectation_commutator_firstVariation_eq_integral
    (expectation : NormalizedExpectation H)
    (V : ℝ → (H →L[ℂ] H)) (A : H →L[ℂ] H) (t : ℝ)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation U V) MeasureTheory.volume 0 t) :
    expectation
        ⁅heisenbergEvolution U t A,
          timeDependentPropagatorFirstVariation U hbar V t⁆ =
      (-(Complex.I / (hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          expectation
            ⁅heisenbergEvolution U t A,
              timeDependentInteractionPerturbation U V s⁆ := by
  let L := commutatorExpectation expectation (heisenbergEvolution U t A)
  have hmap := ContinuousLinearMap.intervalIntegral_comp_comm L hInt
  calc
    expectation
        ⁅heisenbergEvolution U t A,
          timeDependentPropagatorFirstVariation U hbar V t⁆ =
        L (timeDependentPropagatorFirstVariation U hbar V t) := by
      simp [L, commutatorExpectation_apply]
    _ = L ((-(Complex.I / (hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          timeDependentInteractionPerturbation U V s) := by
      rfl
    _ = (-(Complex.I / (hbar : ℂ))) •
        L (∫ s in (0 : ℝ)..t,
          timeDependentInteractionPerturbation U V s) := by
      rw [map_smul]
    _ = (-(Complex.I / (hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          L (timeDependentInteractionPerturbation U V s) := by
      rw [hmap]
    _ = (-(Complex.I / (hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          expectation
            ⁅heisenbergEvolution U t A,
              timeDependentInteractionPerturbation U V s⁆ := by
      simp [L, commutatorExpectation_apply]

/-- The general bounded Kubo formula for the pullback of an ordinary expectation by a pointwise
Hermitian, interval-integrable perturbation. -/
theorem hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound_kubo
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (A : H →L[ℂ] H) {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation U V) MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ =>
        timeDependentPerturbedExpectationFunctional U hbar expectation V lam t A)
      ((-(Complex.I / (hbar : ℂ))) •
        ∫ s in (0 : ℝ)..t,
          expectation
            ⁅heisenbergEvolution U t A,
              timeDependentInteractionPerturbation U V s⁆)
      0 := by
  have h :=
    hasDerivAt_timeDependentPerturbedExpectationFunctional_apply_zero_of_bound_of_isSelfAdjoint
      U hbar expectation hVself A hM hV ht
  rw [expectation_commutator_firstVariation_eq_integral
    U hbar expectation V A t hInt] at h
  exact h

end
end LinearResponse
end QuantumTheory
