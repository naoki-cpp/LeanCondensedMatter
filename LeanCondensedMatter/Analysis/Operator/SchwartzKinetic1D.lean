import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Complex Schwartz differentiation and multiplication

Generic linear endomorphisms of complex Schwartz space and their product/commutation identities.
No Schrödinger Hamiltonian, velocity, Planck constant, or one-particle current is defined here.
The concrete physical specialization lives in `QuantumMechanics.SingleParticle.Continuum.SchwartzSchrodinger1D`.
-/

namespace SchwartzKinetic1D

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

/-- Complex Schwartz functions on the real line. -/
abbrev Space := SchwartzMap ℝ ℂ

/-- Spatial differentiation on complex Schwartz space. -/
noncomputable def derivative : Space →ₗ[ℂ] Space :=
  (SchwartzMap.derivCLM ℂ ℂ).toLinearMap

@[simp]
theorem derivative_apply (f : Space) (x : ℝ) :
    derivative f x = deriv f x :=
  rfl

/-- Multiplication by a fixed complex Schwartz function. -/
noncomputable def multiplicationOperator (f : Space) : Space →ₗ[ℂ] Space where
  toFun := fun ψ => SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f ψ
  map_add' := by
    intro ψ χ
    ext x
    simp
  map_smul' := by
    intro c ψ
    ext x
    simp

@[simp]
theorem multiplicationOperator_apply (f ψ : Space) (x : ℝ) :
    multiplicationOperator f ψ x = f x * ψ x :=
  rfl

/-- The multiplication operator depends complex-linearly on its Schwartz multiplier. -/
noncomputable def multiplicationLinear : Space →ₗ[ℂ] (Space →ₗ[ℂ] Space) where
  toFun := multiplicationOperator
  map_add' := by
    intro f g
    ext ψ x
    change (f x + g x) * ψ x = f x * ψ x + g x * ψ x
    ring
  map_smul' := by
    intro c f
    ext ψ x
    change c * f x * ψ x = c * (f x * ψ x)
    ring

/-- Differentiation obeys the product rule on Schwartz multiplication. -/
theorem derivative_multiplication_apply (f ψ : Space) :
    derivative (multiplicationOperator f ψ) =
      multiplicationOperator (derivative f) ψ +
        multiplicationOperator f (derivative ψ) := by
  ext x
  change deriv (fun y : ℝ => f y * ψ y) x =
    deriv f x * ψ x + f x * deriv ψ x
  exact ((SchwartzMap.hasDerivAt f x).mul (SchwartzMap.hasDerivAt ψ x)).deriv

/-- The second derivative of a product, bundled entirely in Schwartz space. -/
theorem secondDerivative_multiplication_apply (f ψ : Space) :
    derivative (derivative (multiplicationOperator f ψ)) =
      multiplicationOperator (derivative (derivative f)) ψ +
        (2 : ℂ) • multiplicationOperator (derivative f) (derivative ψ) +
        multiplicationOperator f (derivative (derivative ψ)) := by
  rw [derivative_multiplication_apply]
  rw [map_add]
  rw [derivative_multiplication_apply, derivative_multiplication_apply]
  module

/-- Multiplication operators commute on Schwartz space. -/
theorem multiplicationOperator_comp_comm (f g : Space) :
    (multiplicationOperator f).comp (multiplicationOperator g) =
      (multiplicationOperator g).comp (multiplicationOperator f) := by
  ext ψ x
  change f x * (g x * ψ x) = g x * (f x * ψ x)
  ring


end
end SchwartzKinetic1D
