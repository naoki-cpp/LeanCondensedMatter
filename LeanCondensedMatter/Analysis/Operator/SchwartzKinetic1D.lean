import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Tactic

set_option linter.style.header false

/-!
# One-dimensional Schwartz kinetic and localization operators

This module contains the analysis-only operator identity underlying the conventional current for a
one-dimensional Schrödinger Hamiltonian. On complex Schwartz space, let `D` be differentiation,
`M_f` multiplication by a Schwartz test function, and

```text
H = -κ D² + M_V,
v = 2 (i/ℏ) (-κ) D.
```

Then the local multiplication potential commutes with `M_f`, and the Heisenberg motion of the
localizer satisfies

```text
(i/ℏ) [H, M_f] = 1/2 {M_(D f), v}.
```

Everything here is a linear endomorphism of Schwartz space in its natural Fréchet setting; no `L²`
unbounded-operator domain statement is made. The module is independent of quantum mechanics and
second quantization so both layers may reuse the same identity.
-/

namespace SchwartzKinetic1D

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
    apply LinearMap.ext
    intro ψ
    ext x
    change (f x + g x) * ψ x = f x * ψ x + g x * ψ x
    ring
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro ψ
    ext x
    change c * f x * ψ x = c * (f x * ψ x)
    ring

@[simp]
theorem multiplicationLinear_apply (f : Space) :
    multiplicationLinear f = multiplicationOperator f :=
  rfl

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

/-- Kinetic Schrödinger operator `-κ D²` on Schwartz space. -/
noncomputable def kineticOperator (κ : ℝ) : Space →ₗ[ℂ] Space :=
  (-(κ : ℂ)) • derivative.comp derivative

/-- Multiplication-potential Schrödinger operator `-κ D² + M_V` on Schwartz space. -/
noncomputable def schrodingerOperator (κ : ℝ) (potential : Space) : Space →ₗ[ℂ] Space :=
  kineticOperator κ + multiplicationOperator potential

/-- Velocity associated with `H = -κ D² + V`, namely `v = -2 i κ D / ℏ`. -/
noncomputable def velocityOperator (ℏ κ : ℝ) : Space →ₗ[ℂ] Space :=
  ((2 : ℂ) * (Complex.I / (ℏ : ℂ)) * (-(κ : ℂ))) • derivative

/-- Multiplication operators commute on Schwartz space. -/
theorem multiplicationOperator_comp_comm (f g : Space) :
    (multiplicationOperator f).comp (multiplicationOperator g) =
      (multiplicationOperator g).comp (multiplicationOperator f) := by
  apply LinearMap.ext
  intro ψ
  ext x
  change f x * (g x * ψ x) = g x * (f x * ψ x)
  ring

/-- The local multiplication potential contributes no localization commutator. -/
theorem schrodinger_localization_commutator_eq_kinetic
    (κ : ℝ) (potential f : Space) :
    (schrodingerOperator κ potential).comp (multiplicationOperator f) -
        (multiplicationOperator f).comp (schrodingerOperator κ potential) =
      (kineticOperator κ).comp (multiplicationOperator f) -
        (multiplicationOperator f).comp (kineticOperator κ) := by
  rw [schrodingerOperator]
  apply LinearMap.ext
  intro ψ
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add]
  have hcomm := congrArg (fun T : Space →ₗ[ℂ] Space => T ψ)
    (multiplicationOperator_comp_comm potential f)
  have hcomm' :
      multiplicationOperator potential (multiplicationOperator f ψ) =
        multiplicationOperator f (multiplicationOperator potential ψ) := by
    simpa only [LinearMap.comp_apply] using hcomm
  rw [hcomm']
  abel

/-- Schrödinger localization has the standard first-order Heisenberg current form
`(i/ℏ)[H,M_f] = 1/2 {M_(D f),v}` on complex Schwartz space. -/
theorem heisenberg_localization_eq_symmetrized_velocity
    (ℏ κ : ℝ) (potential f : Space) :
    (Complex.I / (ℏ : ℂ)) •
        ((schrodingerOperator κ potential).comp (multiplicationOperator f) -
          (multiplicationOperator f).comp (schrodingerOperator κ potential)) =
      (1 / 2 : ℂ) •
        ((multiplicationOperator (derivative f)).comp (velocityOperator ℏ κ) +
          (velocityOperator ℏ κ).comp (multiplicationOperator (derivative f))) := by
  rw [schrodinger_localization_commutator_eq_kinetic]
  apply LinearMap.ext
  intro ψ
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.add_apply, kineticOperator, velocityOperator]
  rw [secondDerivative_multiplication_apply]
  rw [derivative_multiplication_apply]
  simp only [map_smul]
  module

end
end SchwartzKinetic1D
