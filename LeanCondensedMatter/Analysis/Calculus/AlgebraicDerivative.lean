import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option linter.style.header false

/-!
# Weak algebraic derivatives

A family valued in an algebraic vector space over a nontrivially normed field has an
algebraic derivative when every scalar linear functional sees the corresponding ordinary
scalar derivative. This gives a calculus for vector spaces with no chosen topology.
-/

open scoped BigOperators

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup W] [Module 𝕜 W]

/-- Weak derivative for a family valued in an algebraic vector space.

No topology is imposed on `V`. Instead, every algebraic 𝕜-linear functional `V →ₗ[𝕜] 𝕜`
must turn the family into an ordinarily differentiable scalar function with the stated
derivative. -/
def HasAlgebraicDerivAt (F : 𝕜 → V) (F' : V) (A : 𝕜) : Prop :=
  ∀ ℓ : V →ₗ[𝕜] 𝕜, HasDerivAt (fun z => ℓ (F z)) (ℓ F') A

/-- A scalar differentiable coefficient multiplying a fixed algebraic vector has the expected
algebraic derivative. -/
theorem hasAlgebraicDerivAt_smul_const {f : 𝕜 → 𝕜} {f' A : 𝕜}
    (hf : HasDerivAt f f' A) (v : V) :
    HasAlgebraicDerivAt (fun z => f z • v) (f' • v) A := by
  intro ℓ
  simpa only [map_smul] using hf.smul_const (ℓ v)

namespace HasAlgebraicDerivAt

/-- Algebraic derivatives are additive. -/
theorem add {F G : 𝕜 → V} {F' G' : V} {A : 𝕜}
    (hF : HasAlgebraicDerivAt F F' A) (hG : HasAlgebraicDerivAt G G' A) :
    HasAlgebraicDerivAt (fun z => F z + G z) (F' + G') A := by
  intro ℓ
  simpa only [map_add] using (hF ℓ).add (hG ℓ)

/-- A 𝕜-linear map transports algebraic derivatives. -/
theorem map {F : 𝕜 → V} {F' : V} {A : 𝕜}
    (hF : HasAlgebraicDerivAt F F' A) (T : V →ₗ[𝕜] W) :
    HasAlgebraicDerivAt (fun z => T (F z)) (T F') A := by
  intro ℓ
  simpa only [LinearMap.comp_apply] using hF (ℓ.comp T)

/-- Multiplying an algebraic-vector-valued family by a constant scalar multiplies its derivative. -/
theorem const_smul {F : 𝕜 → V} {F' : V} {A : 𝕜}
    (hF : HasAlgebraicDerivAt F F' A) (c : 𝕜) :
    HasAlgebraicDerivAt (fun z => c • F z) (c • F') A := by
  intro ℓ
  simpa only [map_smul, smul_eq_mul] using (hF ℓ).const_mul c

/-- Reparametrizing an algebraic-vector-valued family by a scalar differentiable map obeys the
chain rule. -/
theorem comp {F : 𝕜 → V} {F' : V} {g : 𝕜 → 𝕜} {g' A : 𝕜}
    (hF : HasAlgebraicDerivAt F F' (g A)) (hg : HasDerivAt g g' A) :
    HasAlgebraicDerivAt (fun z => F (g z)) (g' • F') A := by
  intro ℓ
  simpa only [map_smul, smul_eq_mul, mul_comm, Function.comp_def] using
    (hF ℓ).comp A hg

/-- Finite sums preserve algebraic derivatives. -/
theorem sum {ι : Type*} (s : Finset ι) {F : ι → 𝕜 → V} {F' : ι → V} {A : 𝕜}
    (hF : ∀ i ∈ s, HasAlgebraicDerivAt (F i) (F' i) A) :
    HasAlgebraicDerivAt (fun z => ∑ i ∈ s, F i z) (∑ i ∈ s, F' i) A := by
  classical
  intro ℓ
  simpa only [map_sum] using HasDerivAt.fun_sum (fun i hi => hF i hi ℓ)

end HasAlgebraicDerivAt
