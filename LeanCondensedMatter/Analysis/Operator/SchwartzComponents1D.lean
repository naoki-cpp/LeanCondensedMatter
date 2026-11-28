import LeanCondensedMatter.Analysis.Algebra.FiniteComponents
import LeanCondensedMatter.Analysis.Operator.SchwartzKinetic1D

set_option linter.style.header false

/-!
# Finite-component Schwartz operator algebra

Scalar Schwartz multiplication is lifted to indexed Schwartz states using the general
componentwise linear map from the algebra layer.
-/

namespace SchwartzComponents1D

noncomputable section

/-- Scalar complex Schwartz space used for each internal component. -/
abbrev Spatial := SchwartzKinetic1D.Space

/-- Complex Schwartz states indexed by internal components. -/
abbrev State (ι : Type*) := ι → Spatial

variable {ι : Type*}

/-- Componentwise multiplication by a scalar Schwartz localizer. -/
noncomputable def multiplicationOperator (f : Spatial) : State ι →ₗ[ℂ] State ι :=
  (SchwartzKinetic1D.multiplicationOperator f).compLeft ι

@[simp]
theorem multiplicationOperator_apply
    (f : Spatial) (ψ : State ι) (a : ι) (x : ℝ) :
    multiplicationOperator f ψ a x = f x * ψ a x :=
  rfl

/-- Multiplication localizers depend complex-linearly on the scalar Schwartz test function. -/
noncomputable def multiplicationLinear : Spatial →ₗ[ℂ] (State ι →ₗ[ℂ] State ι) :=
  (FiniteComponents.componentwiseLinear ι).comp SchwartzKinetic1D.multiplicationLinear

end
end SchwartzComponents1D
