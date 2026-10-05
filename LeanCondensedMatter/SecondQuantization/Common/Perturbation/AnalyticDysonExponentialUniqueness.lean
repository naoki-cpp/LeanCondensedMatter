import LeanCondensedMatter.Analysis.Dyson.Uniqueness
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonExponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Volterra uniqueness for the interaction-picture Dyson evolution

The generic interaction-picture Dyson evolution and the ordered operator-exponential candidate solve the same bounded
interaction-picture Volterra equation. The generic uniqueness theorem identifies them on every
compact nonnegative time interval.
-/

namespace SecondQuantization
namespace Common

open Set

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The exact operator-exponential candidate satisfies its interaction-picture Volterra equation,
by the fundamental theorem of calculus. -/
private theorem analyticDysonExponentialCandidate_eq_one_sub_integral (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (lam : ℂ) :
    analyticDysonExponentialCandidate energy V τ lam =
      1 - lam • ∫ σ in (0 : ℝ)..τ,
        continuousInteractionPicture energy V σ *
          analyticDysonExponentialCandidate energy V σ lam := by
  let U : ℝ → FiniteContinuousOperator Config :=
    fun σ => analyticDysonExponentialCandidate energy V σ lam
  let f : ℝ → FiniteContinuousOperator Config :=
    fun σ => -(lam • (continuousInteractionPicture energy V σ * U σ))
  have hderiv : ∀ σ ∈ uIcc (0 : ℝ) τ, HasDerivAt U (f σ) σ := by
    intro σ _
    exact hasDerivAt_analyticDysonExponentialCandidate_interactionPicture
      energy V σ lam
  have hUcont : Continuous U := by
    exact continuous_iff_continuousAt.2 fun σ =>
      (hasDerivAt_analyticDysonExponentialCandidate_interactionPicture
        energy V σ lam).continuousAt
  have hf : Continuous f := by
    have hlam : Continuous (fun _ : ℝ => lam) := continuous_const
    exact (hlam.smul
      ((continuous_continuousInteractionPicture energy V).mul hUcont)).neg
  have hFTC : (∫ σ in (0 : ℝ)..τ, f σ) = U τ - U 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hf.intervalIntegrable 0 τ)
  have hzero : U 0 = 1 := by
    simp [U]
  rw [hzero] at hFTC
  have hFTC' :
      -(lam • ∫ σ in (0 : ℝ)..τ, continuousInteractionPicture energy V σ * U σ) =
        U τ - 1 := by
    simpa only [f, intervalIntegral.integral_neg, intervalIntegral.integral_smul] using hFTC
  change U τ = 1 - lam • ∫ σ in (0 : ℝ)..τ,
    continuousInteractionPicture energy V σ * U σ
  calc
    U τ = 1 + (U τ - 1) := by abel
    _ = 1 + (-(lam • ∫ σ in (0 : ℝ)..τ,
          continuousInteractionPicture energy V σ * U σ)) := by rw [← hFTC']
    _ = 1 - lam • ∫ σ in (0 : ℝ)..τ,
          continuousInteractionPicture energy V σ * U σ := by abel

/-- On every compact nonnegative time interval, the interaction-picture Dyson evolution equals
the exact ordered operator-exponential candidate. -/
private theorem dysonEvolution_eq_exponentialCandidate (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    Dyson.evolution (continuousInteractionPicture energy V) lam τ =
      analyticDysonExponentialCandidate energy V τ lam := by
  have hUcont : Continuous
      (fun t : ℝ => analyticDysonExponentialCandidate energy V t lam) := by
    exact continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_analyticDysonExponentialCandidate_interactionPicture
        energy V t lam).continuousAt
  obtain ⟨M, hBound⟩ := Dyson.exists_continuousBoundedInteraction
    (continuousInteractionPicture energy V) hβ
    (continuous_continuousInteractionPicture energy V)
    ContinuousLinearMap.norm_id_le
  have hEq := Dyson.eqOn_evolution_of_volterra_of_bound
    (V := continuousInteractionPicture energy V)
    (U := fun t : ℝ => analyticDysonExponentialCandidate energy V t lam)
    hβ hBound lam
    hUcont.continuousOn
    (fun t _ => analyticDysonExponentialCandidate_eq_one_sub_integral energy V t lam)
  change Dyson.evolution (continuousInteractionPicture energy V) lam τ =
    analyticDysonExponentialCandidate energy V τ lam
  exact (hEq hτ).symm

/-- For nonnegative imaginary time, the interaction-picture Dyson evolution is the ordered product
of the free and interacting operator exponentials. -/
theorem dysonEvolution_eq_ordered_exp (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    {τ : ℝ} (hτ : 0 ≤ τ) (lam : ℂ) :
    Dyson.evolution (continuousInteractionPicture energy V) lam τ =
      NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) := by
  simpa [analyticDysonExponentialCandidate] using
    dysonEvolution_eq_exponentialCandidate
      (β := τ) (τ := τ) energy V hτ ⟨hτ, le_rfl⟩ lam

/-- At the thermal endpoint, left multiplication by the inverse free evolution leaves the
interacting Gibbs exponential. -/
theorem continuousDiagonalEvolution_neg_mul_dysonEvolution_eq_exp
    (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    {β : ℝ} (hβ : 0 ≤ β) (lam : ℂ) :
    continuousDiagonalEvolution energy (-β) *
        Dyson.evolution (continuousInteractionPicture energy V) lam β =
      NormedSpace.exp ((-β) • continuousInteractingHamiltonian energy V lam) := by
  rw [dysonEvolution_eq_ordered_exp energy V hβ lam]
  rw [← continuousDiagonalEvolution_eq_exp energy β]
  have hinv :
      continuousDiagonalEvolution energy (-β) *
        continuousDiagonalEvolution energy β = 1 := by
    change (continuousDiagonalEvolution energy (-β)).comp
      (continuousDiagonalEvolution energy β) = 1
    exact continuousDiagonalEvolution_neg_comp energy β
  calc
    continuousDiagonalEvolution energy (-β) *
        (continuousDiagonalEvolution energy β *
          NormedSpace.exp (β • (- continuousInteractingHamiltonian energy V lam))) =
      (continuousDiagonalEvolution energy (-β) *
        continuousDiagonalEvolution energy β) *
          NormedSpace.exp (β • (- continuousInteractingHamiltonian energy V lam)) := by
        rw [mul_assoc]
    _ = NormedSpace.exp (β • (- continuousInteractingHamiltonian energy V lam)) := by
      rw [hinv, one_mul]
    _ = NormedSpace.exp ((-β) • continuousInteractingHamiltonian energy V lam) := by
      congr 1
      simp [smul_neg, neg_smul]

end
end Common
end SecondQuantization
