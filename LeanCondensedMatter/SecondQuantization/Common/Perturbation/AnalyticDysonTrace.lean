import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonExponentialUniqueness
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

/-- The `(m,n)` matrix coefficient of a finite continuous operator, bundled as a continuous linear
functional of the operator. -/
noncomputable def finiteOperatorMatrixCoeff (m n : Config) :
    FiniteContinuousOperator Config →L[ℂ] ℂ :=
  (finiteAnalyticCoordinate m).comp
    (ContinuousLinearMap.apply ℂ (FiniteAnalyticFock Config) (finiteAnalyticBasis n))

@[simp]
theorem finiteOperatorMatrixCoeff_apply (m n : Config)
    (A : FiniteContinuousOperator Config) :
    finiteOperatorMatrixCoeff m n A = A (finiteAnalyticBasis n) m := rfl

/-- The ordinary finite-dimensional trace, bundled as a continuous linear functional on the
continuous-operator algebra. -/
noncomputable def finiteOperatorTrace :
    FiniteContinuousOperator Config →L[ℂ] ℂ :=
  ∑ n : Config, finiteOperatorMatrixCoeff n n

@[simp]
theorem finiteOperatorTrace_apply (A : FiniteContinuousOperator Config) :
    finiteOperatorTrace A = ∑ n : Config, A (finiteAnalyticBasis n) n := by
  simp [finiteOperatorTrace]

/-- The continuous trace agrees with the existing algebraic `traceFock` after transport. -/
theorem finiteOperatorTrace_finiteContinuousOperator
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteOperatorTrace (finiteContinuousOperator A) = traceFock A := by
  simp [finiteOperatorTrace_apply, traceFock, finiteContinuousOperator_basis_apply]

/-- Left composition by a fixed finite operator, bundled as a continuous linear map on the
operator algebra. -/
noncomputable def finiteOperatorLeftComp (L : FiniteContinuousOperator Config) :
    FiniteContinuousOperator Config →L[ℂ] FiniteContinuousOperator Config :=
  IsBoundedLinearMap.toContinuousLinearMap
    (fun A : FiniteContinuousOperator Config => L.comp A)
    { map_add := by
        intro A B
        ext x
        simp
      map_smul := by
        intro c A
        ext x
        simp
      bound := by
        refine ⟨max ‖L‖ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun A => ?_⟩
        exact (L.opNorm_comp_le A).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg A)) }

@[simp]
theorem finiteOperatorLeftComp_apply (L A : FiniteContinuousOperator Config) :
    finiteOperatorLeftComp L A = L.comp A := rfl

/-- Trace after left composition by a fixed operator. -/
noncomputable def finiteOperatorTraceLeft (L : FiniteContinuousOperator Config) :
    FiniteContinuousOperator Config →L[ℂ] ℂ :=
  finiteOperatorTrace.comp (finiteOperatorLeftComp L)

@[simp]
theorem finiteOperatorTraceLeft_apply (L A : FiniteContinuousOperator Config) :
    finiteOperatorTraceLeft L A = finiteOperatorTrace (L.comp A) := rfl

/-- Tracing the free evolution composed with a continuous Dyson coefficient gives the existing
algebraic Dyson trace coefficient. -/
theorem finiteOperatorTraceLeft_continuousDysonCoeff (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    finiteOperatorTraceLeft (continuousDiagonalEvolution energy (-β))
        (continuousDysonCoeff energy V n β) =
      dysonTraceCoeff energy β V n := by
  rw [finiteOperatorTraceLeft_apply]
  change finiteOperatorTrace
      ((finiteContinuousOperator (diagonalEvolution energy (-β))).comp
        (finiteContinuousOperator (dysonCoeff energy V n β))) = _
  rw [← finiteContinuousOperator_comp, finiteOperatorTrace_finiteContinuousOperator]
  rfl

/-- The scalar Dyson trace series converges to the trace of the free evolution composed with the
analytic Dyson evolution. -/
theorem hasSum_dysonTraceCoeff_eq_trace_analyticDysonEvolution
    (energy : Config → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    HasSum (fun n : ℕ => lam ^ n * dysonTraceCoeff energy β V n)
      (finiteOperatorTrace
        ((continuousDiagonalEvolution energy (-β)).comp
          (analyticDysonEvolution energy V β lam))) := by
  have h := (hasSum_analyticDysonEvolution
    (β := β) (τ := β) energy V hβ ⟨hβ, le_rfl⟩ lam).map
      (finiteOperatorTraceLeft (continuousDiagonalEvolution energy (-β)))
      (finiteOperatorTraceLeft (continuousDiagonalEvolution energy (-β))).continuous
  have hterms :
      (finiteOperatorTraceLeft (continuousDiagonalEvolution energy (-β)) ∘
        analyticDysonTerm energy V β lam) =
      (fun n : ℕ => lam ^ n * dysonTraceCoeff energy β V n) := by
    funext n
    change finiteOperatorTraceLeft (continuousDiagonalEvolution energy (-β))
        (lam ^ n • continuousDysonCoeff energy V n β) =
      lam ^ n * dysonTraceCoeff energy β V n
    rw [map_smul, smul_eq_mul,
      finiteOperatorTraceLeft_continuousDysonCoeff]
  rw [hterms] at h
  exact h

end
end Common
end SecondQuantization
