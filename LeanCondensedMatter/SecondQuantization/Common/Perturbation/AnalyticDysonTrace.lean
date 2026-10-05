import LeanCondensedMatter.Analysis.Dyson.Bounds
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDyson
import Mathlib.Analysis.Normed.Operator.Mul
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries

set_option linter.style.header false

/-!
# Continuous traces of the analytic Dyson evolution

The algebraic trace `traceFock` is transported to the finite-dimensional continuous-operator
realization as a genuine continuous linear map. This lets convergent operator-valued Dyson sums be
mapped directly to convergent scalar trace series.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The scalar Dyson trace series converges to the trace of the free evolution composed with the
analytic Dyson evolution. -/
theorem hasSum_dysonTraceCoeff
    (energy : Config → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    HasSum (fun n : ℕ => lam ^ n * dysonTraceCoeff energy β V n)
      (finiteOperatorTrace
        ((continuousDiagonalEvolution energy (-β)).comp
          (analyticDysonEvolution energy V β lam))) := by
  obtain ⟨M, hBound⟩ := Dyson.exists_continuousBoundedInteraction
    (continuousInteractionPicture energy V) hβ
    (continuous_continuousInteractionPicture energy V)
    ContinuousLinearMap.norm_id_le
  let traceLeft : FiniteContinuousOperator Config →L[ℂ] ℂ :=
    finiteOperatorTrace.comp
      ((ContinuousLinearMap.mul ℂ (FiniteContinuousOperator Config))
        (continuousDiagonalEvolution energy (-β)))
  have htrace (n : ℕ) :
      traceLeft (Dyson.coeff (continuousInteractionPicture energy V) n β) =
        dysonTraceCoeff energy β V n := by
    rw [← continuousDysonCoeff_eq_coeff]
    change finiteOperatorTrace
      ((finiteContinuousOperatorAlgEquiv (diagonalEvolution energy (-β))).comp
        (finiteContinuousOperatorAlgEquiv (dysonCoeff energy V n β))) = _
    rw [← ContinuousLinearMap.mul_def, ← map_mul, Module.End.mul_eq_comp,
      finiteOperatorTrace_finiteContinuousOperator]
    rfl
  have h := (Dyson.hasSum_evolution_of_bound
    hBound.toBoundedInteraction lam ⟨hβ, le_rfl⟩).map
      traceLeft traceLeft.continuous
  have hterms :
      (traceLeft ∘ Dyson.term (continuousInteractionPicture energy V) lam β) =
      (fun n : ℕ => lam ^ n * dysonTraceCoeff energy β V n) := by
    funext n
    change traceLeft
        (lam ^ n • Dyson.coeff (continuousInteractionPicture energy V) n β) =
      lam ^ n * dysonTraceCoeff energy β V n
    rw [map_smul, smul_eq_mul, htrace]
  rw [hterms] at h
  simpa [traceLeft, analyticDysonEvolution, ContinuousLinearMap.mul_def] using h

end
end Common
end SecondQuantization
