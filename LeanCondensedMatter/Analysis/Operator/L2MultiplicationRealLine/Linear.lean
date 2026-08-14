import LeanCondensedMatter.Analysis.Operator.L2MultiplicationRealLine

set_option linter.style.header false

/-!
# Linear family of bounded multiplication operators on `L²(ℝ, ℂ)`

This module bundles the real-line `L∞` multiplication construction as a complex-linear family after
forgetting continuity of each operator.  This is the representation-independent interface needed by
algebraic constructions such as second quantization: the same canonical `L²` multiplication
operator remains available as a `ContinuousLinearMap`, while its dependence on the multiplier is
recorded by a `LinearMap`.
-/

namespace L2MultiplicationRealLine

noncomputable section

open MeasureTheory

/-- Multiplication on `L²(ℝ, ℂ)` depends complex-linearly on the `L∞` multiplier, after forgetting
continuity of each individual operator. -/
noncomputable def multiplicationLinear :
    ComplexLInf →ₗ[ℂ] (ComplexL2 →ₗ[ℂ] ComplexL2) where
  toFun := fun f => (multiplicationOperator f).toLinearMap
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro ψ
    change (f + g) • ψ = f • ψ + g • ψ
    exact Lp.smul_add f g ψ
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro ψ
    change (c • f) • ψ = c • (f • ψ)
    exact Lp.smul_assoc c f ψ

@[simp]
theorem multiplicationLinear_apply (f : ComplexLInf) (ψ : ComplexL2) :
    multiplicationLinear f ψ = multiplicationOperator f ψ :=
  rfl

end
end L2MultiplicationRealLine
