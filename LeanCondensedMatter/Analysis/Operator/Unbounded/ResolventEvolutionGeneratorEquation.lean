import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolutionGenerator

set_option linter.style.header false

/-!
# Strong generator equation for the limiting Stone evolution

The derivative at zero is transported to arbitrary time by the one-parameter group law.  The
already-proved domain invariance and generator intertwining then rewrite the derivative as
`-i A (U(t)x)` on the preserved original domain.
-/

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The limiting evolution satisfies its strong generator equation at arbitrary time, with the
right-hand side written as the evolved generator. -/
theorem resolventEvolutionStrongLimitOperator_apply_hasDerivAt_intertwined
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) (s : ℝ) :
    HasDerivAt (fun t : ℝ => resolventEvolutionStrongLimitOperator A hA t (x : H))
      ((-I : ℂ) • resolventEvolutionStrongLimitOperator A hA s (A x)) s := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hzero :=
    (resolventEvolutionStrongLimitOperator_apply_hasDerivAt_zero A hA x).tendsto_slope_zero
  have hmapped :
      Tendsto
        (fun h : ℝ =>
          resolventEvolutionStrongLimitOperator A hA s
            (h⁻¹ •
              (resolventEvolutionStrongLimitOperator A hA (0 + h) (x : H) -
                resolventEvolutionStrongLimitOperator A hA 0 (x : H))))
        (𝓝[≠] 0)
        (𝓝 (resolventEvolutionStrongLimitOperator A hA s ((-I : ℂ) • A x))) := by
    exact ((resolventEvolutionStrongLimitOperator A hA s).continuous.tendsto _).comp hzero
  have hfun :
      (fun h : ℝ =>
        h⁻¹ •
          (resolventEvolutionStrongLimitOperator A hA (s + h) (x : H) -
            resolventEvolutionStrongLimitOperator A hA s (x : H))) =
      (fun h : ℝ =>
        resolventEvolutionStrongLimitOperator A hA s
          (h⁻¹ •
            (resolventEvolutionStrongLimitOperator A hA (0 + h) (x : H) -
              resolventEvolutionStrongLimitOperator A hA 0 (x : H)))) := by
    funext h
    rw [show
      resolventEvolutionStrongLimitOperator A hA (s + h) (x : H) =
        resolventEvolutionStrongLimitOperator A hA s
          (resolventEvolutionStrongLimitOperator A hA h (x : H)) by
      simpa only [resolventEvolutionStrongLimitOperator_apply] using
        resolventEvolutionStrongLimit_add_time_apply A hA s h (x : H)]
    rw [show resolventEvolutionStrongLimitOperator A hA 0 (x : H) = (x : H) by
      simpa only [resolventEvolutionStrongLimitOperator_apply] using
        resolventEvolutionStrongLimit_zero_apply A hA (x : H)]
    simp only [zero_add]
    rw [← (resolventEvolutionStrongLimitOperator A hA s).map_sub]
    symm
    exact (resolventEvolutionStrongLimitOperator A hA s).toLinearMap.map_smul_of_tower
      h⁻¹ (resolventEvolutionStrongLimitOperator A hA h (x : H) - (x : H))
  rw [hfun]
  have hmapgen :
      resolventEvolutionStrongLimitOperator A hA s ((-I : ℂ) • A x) =
        (-I : ℂ) • resolventEvolutionStrongLimitOperator A hA s (A x) := by
    exact (resolventEvolutionStrongLimitOperator A hA s).map_smul _ _
  rw [hmapgen] at hmapped
  exact hmapped

/-- Strong Stone derivative on the preserved generator domain. -/
theorem resolventEvolutionStrongLimitOperator_apply_hasDerivAt
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => resolventEvolutionStrongLimitOperator A hA s (x : H))
      ((-I : ℂ) •
        A ⟨resolventEvolutionStrongLimitOperator A hA t (x : H),
          resolventEvolutionStrongLimitOperator_mem_domain A hA t x⟩) t := by
  have h := resolventEvolutionStrongLimitOperator_apply_hasDerivAt_intertwined A hA x t
  rw [resolventEvolutionStrongLimitOperator_apply_domain A hA t x]
  exact h

end

end LinearPMap
