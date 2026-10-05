import LeanCondensedMatter.Analysis.Dyson.Basic
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDyson

set_option linter.style.header false

/-!
# Convergent analytic Dyson evolution

The finite-dimensional interaction-picture Dyson evolution keeps a domain-level name in
SecondQuantization, while its recursion, convergence, and uniqueness are owned by the
dimension-independent `Analysis.Dyson` API.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The norm-topological interaction-picture Dyson evolution specialized to the finite continuous
operator realization. -/
noncomputable def analyticDysonEvolution (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) : FiniteContinuousOperator Config :=
  Dyson.evolution (continuousInteractionPicture energy V) lam τ

end
end Common
end SecondQuantization
