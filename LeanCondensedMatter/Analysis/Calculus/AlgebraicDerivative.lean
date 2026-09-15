import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Weak algebraic derivatives

A family valued in an algebraic complex vector space has an algebraic derivative when every
complex-linear scalar functional sees the corresponding ordinary complex derivative. This gives a
calculus for vector spaces with no chosen topology.
-/

variable {V W : Type*}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

/-- Weak derivative for a family valued in an algebraic complex vector space.

No topology is imposed on `V`. Instead, every algebraic complex-linear functional `V →ₗ[ℂ] ℂ`
must turn the family into an ordinarily complex-differentiable scalar function with the stated
derivative. -/
def HasAlgebraicDerivAt (F : ℂ → V) (F' : V) (A : ℂ) : Prop :=
  ∀ ℓ : V →ₗ[ℂ] ℂ, HasDerivAt (fun z => ℓ (F z)) (ℓ F') A

/-- A scalar differentiable coefficient multiplying a fixed algebraic vector has the expected
algebraic derivative. -/
theorem hasAlgebraicDerivAt_smul_const {f : ℂ → ℂ} {f' A : ℂ}
    (hf : HasDerivAt f f' A) (v : V) :
    HasAlgebraicDerivAt (fun z => f z • v) (f' • v) A := by
  intro ℓ
  simpa only [map_smul] using hf.smul_const (ℓ v)

namespace HasAlgebraicDerivAt

/-- Algebraic derivatives are additive. -/
theorem add {F G : ℂ → V} {F' G' : V} {A : ℂ}
    (hF : HasAlgebraicDerivAt F F' A) (hG : HasAlgebraicDerivAt G G' A) :
    HasAlgebraicDerivAt (fun z => F z + G z) (F' + G') A := by
  intro ℓ
  simp only [map_add]
  apply ((hF ℓ).add (hG ℓ)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- A complex-linear map transports algebraic derivatives. -/
theorem map {F : ℂ → V} {F' : V} {A : ℂ}
    (hF : HasAlgebraicDerivAt F F' A) (T : V →ₗ[ℂ] W) :
    HasAlgebraicDerivAt (fun z => T (F z)) (T F') A := by
  intro ℓ
  simpa only [LinearMap.comp_apply] using hF (ℓ.comp T)

end HasAlgebraicDerivAt
