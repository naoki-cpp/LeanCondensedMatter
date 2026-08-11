import LeanCondensedMatter.Analysis.Dyson.Uniqueness
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
  let VI : ℝ → (H →L[ℂ] H) := timeDependentInteractionPerturbation system V
  let c : ℂ := timeDependentPhysicalDysonCoupling system lam
  let U : ℝ → (H →L[ℂ] H) := fun s =>
    timeDependentInteractionPropagator system V lam s
  let q : ℝ → (H →L[ℂ] H) := fun s => star (U s) * U s - 1
  have hOne : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have hUcont : ContinuousOn U (Icc (0 : ℝ) β) := by
    simpa [U, VI, c, timeDependentInteractionPropagator] using
      (Dyson.continuousOn_evolution_of_bound hVcont hOne hM hVbound c)
  have hUEq : ∀ s ∈ Icc (0 : ℝ) β,
      U s = 1 - c • ∫ u in (0 : ℝ)..s, VI u * U u := by
    intro s hs
    simpa [U, VI, c, timeDependentInteractionPropagator] using
      (Dyson.evolution_eq_one_sub_integral_of_bound hVcont hOne hM hVbound hs c)
  have hUderiv : ∀ s ∈ Ico (0 : ℝ) β,
      HasDerivWithinAt U (-(c • (VI s * U s))) (Ici s) s := by
    intro s hs
    exact Dyson.hasDerivWithinAt_of_volterra hVcont hβ hs c hUcont hUEq
  have hqcont : ContinuousOn q (Icc (0 : ℝ) β) := by
    exact (hUcont.star.mul hUcont).sub continuousOn_const
  have hqderiv : ∀ s ∈ Ico (0 : ℝ) β,
      HasDerivWithinAt q 0 (Ici s) s := by
    intro s hs
    have hUd := hUderiv s hs
    have hprod := hUd.star.mul hUd
    have hsub := hprod.sub_const (1 : H →L[ℂ] H)
    have hVIstar : star (VI s) = VI s := by
      simpa [VI] using
        (isSelfAdjoint_timeDependentInteractionPerturbation_of_isSelfAdjoint
          system V hVself s).star_eq
    have hc : star c = -c := by
      simpa [c] using star_timeDependentPhysicalDysonCoupling_eq_neg system lam
    have hzero :
        star (-(c • (VI s * U s))) * U s +
            star (U s) * -(c • (VI s * U s)) = 0 := by
      simp [hc, hVIstar, star_smul, star_mul, mul_assoc]
    rw [hzero] at hsub
    simpa [q] using hsub
  have hq0 : q 0 = 0 := by
    simp [q, U, timeDependentInteractionPropagator]
  have hqbound : ∀ s ∈ Ico (0 : ℝ) β,
      ‖(0 : H →L[ℂ] H)‖ ≤ 0 * ‖q s‖ := by
    simp
  have hqzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := q) (f' := fun _ => (0 : H →L[ℂ] H)) (K := 0)
    (a := (0 : ℝ)) (b := β) hqcont hqderiv hq0 hqbound
  have := hqzero t ht
  simpa [q, U, sub_eq_zero] using this

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
  let VI : ℝ → (H →L[ℂ] H) := timeDependentInteractionPerturbation system V
  let c : ℂ := timeDependentPhysicalDysonCoupling system lam
  let U : ℝ → (H →L[ℂ] H) := fun s =>
    timeDependentInteractionPropagator system V lam s
  let q : ℝ → (H →L[ℂ] H) := fun s => U s * star (U s) - 1
  let q' : ℝ → (H →L[ℂ] H) := fun s =>
    c • (q s * VI s - VI s * q s)
  have hOne : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have hUcont : ContinuousOn U (Icc (0 : ℝ) β) := by
    simpa [U, VI, c, timeDependentInteractionPropagator] using
      (Dyson.continuousOn_evolution_of_bound hVcont hOne hM hVbound c)
  have hUEq : ∀ s ∈ Icc (0 : ℝ) β,
      U s = 1 - c • ∫ u in (0 : ℝ)..s, VI u * U u := by
    intro s hs
    simpa [U, VI, c, timeDependentInteractionPropagator] using
      (Dyson.evolution_eq_one_sub_integral_of_bound hVcont hOne hM hVbound hs c)
  have hUderiv : ∀ s ∈ Ico (0 : ℝ) β,
      HasDerivWithinAt U (-(c • (VI s * U s))) (Ici s) s := by
    intro s hs
    exact Dyson.hasDerivWithinAt_of_volterra hVcont hβ hs c hUcont hUEq
  have hqcont : ContinuousOn q (Icc (0 : ℝ) β) := by
    exact (hUcont.mul hUcont.star).sub continuousOn_const
  have hqderiv : ∀ s ∈ Ico (0 : ℝ) β,
      HasDerivWithinAt q (q' s) (Ici s) s := by
    intro s hs
    have hUd := hUderiv s hs
    have hprod := hUd.mul hUd.star
    have hsub := hprod.sub_const (1 : H →L[ℂ] H)
    have hVIstar : star (VI s) = VI s := by
      simpa [VI] using
        (isSelfAdjoint_timeDependentInteractionPerturbation_of_isSelfAdjoint
          system V hVself s).star_eq
    have hc : star c = -c := by
      simpa [c] using star_timeDependentPhysicalDysonCoupling_eq_neg system lam
    have hstar :
        star (-(c • (VI s * U s))) = c • (star (U s) * VI s) := by
      simp [hc, hVIstar, star_smul, star_mul]
    have hcomm :
        -(c • (VI s * U s)) * star (U s) +
            U s * star (-(c • (VI s * U s))) = q' s := by
      rw [hstar]
      simp only [q', q]
      noncomm_ring
      module
    rw [hcomm] at hsub
    simpa [q] using hsub
  have hq0 : q 0 = 0 := by
    simp [q, U, timeDependentInteractionPropagator]
  have hqbound : ∀ s ∈ Ico (0 : ℝ) β,
      ‖q' s‖ ≤ (2 * ‖c‖ * M) * ‖q s‖ := by
    intro s hs
    have hsIcc : s ∈ Icc (0 : ℝ) β := ⟨hs.1, hs.2.le⟩
    rw [show q' s = c • (q s * VI s - VI s * q s) by rfl, norm_smul]
    calc
      ‖c‖ * ‖q s * VI s - VI s * q s‖ ≤
          ‖c‖ * (‖q s * VI s‖ + ‖VI s * q s‖) := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ‖c‖ * (‖q s‖ * M + M * ‖q s‖) := by
        gcongr
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left (hVbound s hsIcc) (norm_nonneg _))
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hVbound s hsIcc) (norm_nonneg _))
      _ = (2 * ‖c‖ * M) * ‖q s‖ := by ring
  have hqzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := q) (f' := q') (K := 2 * ‖c‖ * M)
    (a := (0 : ℝ)) (b := β) hqcont hqderiv hq0 hqbound
  have := hqzero t ht
  simpa [q, U, sub_eq_zero] using this

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
