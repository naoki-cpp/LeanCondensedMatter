import LeanCondensedMatter.Analysis.Dyson.Unitary
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.KuboFormula

set_option linter.style.header false

/-!
# Unitarity of Hermitian time-dependent Dyson evolution

For the physical coupling in

`H_λ(t) = H₀ + λ V(t)`, `λ ∈ ℝ`,

the Dyson scalar is `c = λ i / ℏ`, hence `c† = -c`. If `V(t)` is pointwise self-adjoint, then the
interaction-picture perturbation is also pointwise self-adjoint. The Volterra equation gives

`U'(t) = -c V_I(t) U(t)`.

The left product has zero derivative,

`(U(t)† U(t))' = 0`,

while the right-product defect `Q(t) = U(t) U(t)† - 1` satisfies the homogeneous commutator
ordinary differential equation

`Q'(t) = c (Q(t) V_I(t) - V_I(t) Q(t))`.

Both defects vanish initially. The existing vector-valued Grönwall theorem therefore proves the
two unitary identities on every compact nonnegative interval where the continuity and boundedness
hypotheses hold. The left identity also proves that the finite-coupling observable map is unital, so
the ordinary expectation can be pulled back through the canonical `NormalizedExpectation` API.
-/

namespace QuantumTheory
namespace LinearResponse

open Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)

/-- The physical Dyson scalar for a real coupling is skew-adjoint. -/
theorem star_timeDependentPhysicalDysonCoupling_eq_neg (lam : ℝ) :
    star (timeDependentPhysicalDysonCoupling hbar lam) =
      -timeDependentPhysicalDysonCoupling hbar lam := by
  unfold timeDependentPhysicalDysonCoupling
  rw [Complex.star_def]
  simp
  ring_nf

private theorem continuousTimeDependentDysonInteraction
    {V : ℝ → (H →L[ℂ] H)} {β M : ℝ} (hM : 0 ≤ M)
    (hVcont : Continuous (timeDependentInteractionPerturbation U V))
    (hVbound : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M) :
    Dyson.ContinuousBoundedInteraction
      (timeDependentInteractionPerturbation U V) β M := by
  exact
    { toBoundedInteraction :=
        { norm_one_le := by
            change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
            exact ContinuousLinearMap.norm_id_le
          bound_nonneg := hM
          interaction_norm_le := hVbound }
      interaction_continuous := hVcont }

/-- The two unitary identities for the physical interaction-picture Dyson propagator. -/
theorem timeDependentInteractionPropagator_unitary_relations_of_isSelfAdjoint
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (lam : ℝ) {β M t : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hVcont : Continuous (timeDependentInteractionPerturbation U V))
    (hVbound : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    star (timeDependentInteractionPropagator U hbar V lam t) *
          timeDependentInteractionPropagator U hbar V lam t = 1 ∧
      timeDependentInteractionPropagator U hbar V lam t *
          star (timeDependentInteractionPropagator U hbar V lam t) = 1 := by
  apply Dyson.evolution_unitary_relations_of_star_eq
    (V := timeDependentInteractionPerturbation U V)
    (lam := timeDependentPhysicalDysonCoupling hbar lam)
    (β := β) (M := M) (t := t)
  · intro s
    exact (isSelfAdjoint_timeDependentInteractionPerturbation_of_isSelfAdjoint U V hVself s).star_eq
  · exact star_timeDependentPhysicalDysonCoupling_eq_neg hbar lam
  · exact hβ
  · exact continuousTimeDependentDysonInteraction U hM hVcont hVbound
  · exact ht

/-- For a pointwise Hermitian perturbation, the finite-coupling observable map preserves the
identity. This is the exact hypothesis needed to pull back a normalized expectation. -/
theorem timeDependentPerturbedObservableMap_one_of_isSelfAdjoint
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (lam : ℝ) {β M t : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hVcont : Continuous (timeDependentInteractionPerturbation U V))
    (hVbound : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    timeDependentPerturbedObservableMap U hbar V lam t 1 = 1 := by
  rw [timeDependentPerturbedObservableMap_apply]
  simp only [timeDependentPerturbedObservable, map_one, mul_one]
  exact (timeDependentInteractionPropagator_unitary_relations_of_isSelfAdjoint
    U hbar hVself lam hβ hM hVcont hVbound ht).1

/-- The finite-coupling perturbed expectation is the pullback of the ordinary expectation along the
unital perturbed-observable map. -/
noncomputable def timeDependentPerturbedNormalizedExpectation
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (lam : ℝ) {β M t : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hVcont : Continuous (timeDependentInteractionPerturbation U V))
    (hVbound : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) : NormalizedExpectation H :=
  expectation.pullback (timeDependentPerturbedObservableMap U hbar V lam t)
    (timeDependentPerturbedObservableMap_one_of_isSelfAdjoint
      U hbar hVself lam hβ hM hVcont hVbound ht)

@[simp]
theorem timeDependentPerturbedNormalizedExpectation_apply
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (lam : ℝ) {β M t : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hVcont : Continuous (timeDependentInteractionPerturbation U V))
    (hVbound : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation U V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) (A : H →L[ℂ] H) :
    timeDependentPerturbedNormalizedExpectation U hbar expectation hVself lam
        hβ hM hVcont hVbound ht A =
      expectation (timeDependentPerturbedObservable U hbar V A lam t) := by
  simp [timeDependentPerturbedNormalizedExpectation,
    timeDependentPerturbedObservableMap_apply]

end
end LinearResponse
end QuantumTheory
