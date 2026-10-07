import LeanCondensedMatter.Analysis.Dyson.Unitary
import LeanCondensedMatter.QuantumTheory.LinearResponse.KuboFormula

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

variable (system : BoundedFreeSystem H)

/-- The physical Dyson scalar for a real coupling is skew-adjoint. -/
theorem star_timeDependentPhysicalDysonCoupling_eq_neg (lam : ℝ) :
    star (timeDependentPhysicalDysonCoupling system lam) =
      -timeDependentPhysicalDysonCoupling system lam := by
  unfold timeDependentPhysicalDysonCoupling
  rw [Complex.star_def]
  simp
  ring_nf

private theorem continuousTimeDependentDysonInteraction
    {V : ℝ → (H →L[ℂ] H)} {β M : ℝ} (hM : 0 ≤ M)
    (hVcont : Continuous (timeDependentInteractionPerturbation system V))
    (hVbound : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M) :
    Dyson.ContinuousBoundedInteraction
      (timeDependentInteractionPerturbation system V) β M := by
  exact
    { toBoundedInteraction :=
        { norm_one_le := by
            change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
            exact ContinuousLinearMap.norm_id_le
          bound_nonneg := hM
          interaction_norm_le := hVbound }
      interaction_continuous := hVcont }

/-- For a pointwise Hermitian perturbation, the interaction-picture Dyson propagator satisfies
`U(t)† U(t) = 1` on the compact nonnegative interval where the Volterra hypotheses hold. -/
theorem star_mul_timeDependentInteractionPropagator_eq_one_of_isSelfAdjoint
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (lam : ℝ) {β M t : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hVcont : Continuous (timeDependentInteractionPerturbation system V))
    (hVbound : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    star (timeDependentInteractionPropagator system V lam t) *
        timeDependentInteractionPropagator system V lam t = 1 := by
  apply Dyson.star_mul_evolution_eq_one_of_star_eq
    (V := timeDependentInteractionPerturbation system V)
    (lam := timeDependentPhysicalDysonCoupling system lam)
    (β := β) (M := M) (t := t)
  · intro s
    exact (isSelfAdjoint_timeDependentInteractionPerturbation_of_isSelfAdjoint
      system V hVself s).star_eq
  · exact star_timeDependentPhysicalDysonCoupling_eq_neg system lam
  · exact hβ
  · exact continuousTimeDependentDysonInteraction system hM hVcont hVbound
  · exact ht

/-- For a pointwise Hermitian perturbation, the interaction-picture Dyson propagator also satisfies
`U(t) U(t)† = 1`. The proof applies Grönwall to the right-product defect, whose derivative is a
homogeneous commutator with `V_I(t)`. -/
theorem mul_star_timeDependentInteractionPropagator_eq_one_of_isSelfAdjoint
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (lam : ℝ) {β M t : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hVcont : Continuous (timeDependentInteractionPerturbation system V))
    (hVbound : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    timeDependentInteractionPropagator system V lam t *
        star (timeDependentInteractionPropagator system V lam t) = 1 := by
  apply Dyson.mul_star_evolution_eq_one_of_star_eq
    (V := timeDependentInteractionPerturbation system V)
    (lam := timeDependentPhysicalDysonCoupling system lam)
    (β := β) (M := M) (t := t)
  · intro s
    exact (isSelfAdjoint_timeDependentInteractionPerturbation_of_isSelfAdjoint
      system V hVself s).star_eq
  · exact star_timeDependentPhysicalDysonCoupling_eq_neg system lam
  · exact hβ
  · exact continuousTimeDependentDysonInteraction system hM hVcont hVbound
  · exact ht

/-- The two unitary identities for the physical interaction-picture Dyson propagator. -/
theorem timeDependentInteractionPropagator_unitary_relations_of_isSelfAdjoint
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (lam : ℝ) {β M t : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hVcont : Continuous (timeDependentInteractionPerturbation system V))
    (hVbound : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    star (timeDependentInteractionPropagator system V lam t) *
          timeDependentInteractionPropagator system V lam t = 1 ∧
      timeDependentInteractionPropagator system V lam t *
          star (timeDependentInteractionPropagator system V lam t) = 1 := by
  exact ⟨
    star_mul_timeDependentInteractionPropagator_eq_one_of_isSelfAdjoint
      system hVself lam hβ hM hVcont hVbound ht,
    mul_star_timeDependentInteractionPropagator_eq_one_of_isSelfAdjoint
      system hVself lam hβ hM hVcont hVbound ht⟩

/-- For a pointwise Hermitian perturbation, the finite-coupling observable map preserves the
identity. This is the exact hypothesis needed to pull back a normalized expectation. -/
theorem timeDependentPerturbedObservableMap_one_of_isSelfAdjoint
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (lam : ℝ) {β M t : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hVcont : Continuous (timeDependentInteractionPerturbation system V))
    (hVbound : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    timeDependentPerturbedObservableMap system V lam t 1 = 1 := by
  rw [timeDependentPerturbedObservableMap_apply]
  simp [timeDependentPerturbedObservable, heisenbergEvolution,
    freePropagator_neg_mul,
    star_mul_timeDependentInteractionPropagator_eq_one_of_isSelfAdjoint
      system hVself lam hβ hM hVcont hVbound ht]

/-- The finite-coupling perturbed expectation is the pullback of the ordinary expectation along the
unital perturbed-observable map. -/
noncomputable def timeDependentPerturbedNormalizedExpectation
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (lam : ℝ) {β M t : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hVcont : Continuous (timeDependentInteractionPerturbation system V))
    (hVbound : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) : NormalizedExpectation H :=
  expectation.pullback (timeDependentPerturbedObservableMap system V lam t)
    (timeDependentPerturbedObservableMap_one_of_isSelfAdjoint
      system hVself lam hβ hM hVcont hVbound ht)

@[simp]
theorem timeDependentPerturbedNormalizedExpectation_apply
    (expectation : NormalizedExpectation H)
    {V : ℝ → (H →L[ℂ] H)} (hVself : ∀ s, IsSelfAdjoint (V s))
    (lam : ℝ) {β M t : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hVcont : Continuous (timeDependentInteractionPerturbation system V))
    (hVbound : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system V s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β) (A : H →L[ℂ] H) :
    timeDependentPerturbedNormalizedExpectation system expectation hVself lam
        hβ hM hVcont hVbound ht A =
      expectation (timeDependentPerturbedObservable system V A lam t) := by
  simp [timeDependentPerturbedNormalizedExpectation,
    timeDependentPerturbedObservableMap_apply]

end
end LinearResponse
end QuantumTheory
