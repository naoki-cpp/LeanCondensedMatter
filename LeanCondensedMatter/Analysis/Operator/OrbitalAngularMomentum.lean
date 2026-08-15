import LeanCondensedMatter.Analysis.Operator.LinearCommutator
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Algebraic orbital-angular-momentum commutators

This module records the representation-independent linear-map algebra needed to distinguish
continuum-like orbital angular momentum from an internal degree of freedom.

For four endomorphisms playing the roles of `X`, `Y`, `Pₓ`, and `Pᵧ`, define

```text
L_z = X Pᵧ - Y Pₓ.
```

If a localization operator `M` commutes with the position operators, the commutator with `L_z`
reduces to

```text
[M, L_z] = X [M, Pᵧ] - Y [M, Pₓ].
```

Thus any momentum-localization commutator survives directly in the orbital quantity. In the
continuum specialization `Pᵢ = -i ℏ ∂ᵢ`, one has schematically
`[M_f, Pᵢ] = i ℏ M_(∂ᵢ f)`, so continuum orbital angular momentum is not an internal quantity that
may automatically be fed through a localizer-commuting conventional-current theorem.

No unbounded-operator or second-quantization structure is used here.
-/

namespace ConservationLaw

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Leibniz rule for a commutator with a composition on the right:
`[M, A B] = [M,A] B + A [M,B]`. -/
theorem linearCommutator_comp_right
    (M A B : V →ₗ[ℂ] V) :
    linearCommutator M (A.comp B) =
      (linearCommutator M A).comp B + A.comp (linearCommutator M B) := by
  apply LinearMap.ext
  intro v
  simp [linearCommutator]
  module

/-- A commutator is additive over subtraction in its second argument. -/
theorem linearCommutator_sub_right
    (M A B : V →ₗ[ℂ] V) :
    linearCommutator M (A - B) =
      linearCommutator M A - linearCommutator M B := by
  apply LinearMap.ext
  intro v
  simp [linearCommutator]
  module

/-- Algebraic `z` component of orbital angular momentum, `L_z = X Pᵧ - Y Pₓ`.

The inputs are deliberately only complex-linear endomorphisms. Concrete continuum models may later
instantiate them with position and momentum operators on a common invariant test-function space. -/
noncomputable def orbitalAngularMomentumZ
    (X Y Px Py : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  X.comp Py - Y.comp Px

/-- Expansion of a localization commutator with algebraic orbital angular momentum. -/
theorem linearCommutator_orbitalAngularMomentumZ
    (M X Y Px Py : V →ₗ[ℂ] V) :
    linearCommutator M (orbitalAngularMomentumZ X Y Px Py) =
      ((linearCommutator M X).comp Py + X.comp (linearCommutator M Py)) -
        ((linearCommutator M Y).comp Px + Y.comp (linearCommutator M Px)) := by
  rw [orbitalAngularMomentumZ, linearCommutator_sub_right,
    linearCommutator_comp_right, linearCommutator_comp_right]

/-- If localization commutes with position, its orbital commutator is controlled entirely by the
momentum-localization commutators:

`[M,L_z] = X [M,Pᵧ] - Y [M,Pₓ]`.
-/
theorem linearCommutator_orbitalAngularMomentumZ_of_commutes_position
    (M X Y Px Py : V →ₗ[ℂ] V)
    (hX : linearCommutator M X = 0)
    (hY : linearCommutator M Y = 0) :
    linearCommutator M (orbitalAngularMomentumZ X Y Px Py) =
      X.comp (linearCommutator M Py) - Y.comp (linearCommutator M Px) := by
  rw [linearCommutator_orbitalAngularMomentumZ, hX, hY]
  simp

/-- Specialization when the momentum-localization commutators are represented by supplied
"derivative localizer" operators `Dx` and `Dy` with a common scalar coefficient `c`.

For continuum momentum `Pᵢ = -i ℏ ∂ᵢ`, the physical coefficient is `c = i ℏ` and `Di` is
multiplication by `∂ᵢ f`. -/
theorem linearCommutator_orbitalAngularMomentumZ_of_derivative_localizers
    (M X Y Px Py Dx Dy : V →ₗ[ℂ] V) (c : ℂ)
    (hX : linearCommutator M X = 0)
    (hY : linearCommutator M Y = 0)
    (hPx : linearCommutator M Px = c • Dx)
    (hPy : linearCommutator M Py = c • Dy) :
    linearCommutator M (orbitalAngularMomentumZ X Y Px Py) =
      X.comp (c • Dy) - Y.comp (c • Dx) := by
  rw [linearCommutator_orbitalAngularMomentumZ_of_commutes_position M X Y Px Py hX hY,
    hPx, hPy]

/-- Exact nonvanishing criterion under position-localizer commutation.

This makes the obstruction explicit: continuum-like `L_z` fails to commute with localization exactly
when the derivative-localization combination on the right is nonzero. -/
theorem linearCommutator_orbitalAngularMomentumZ_ne_zero_iff
    (M X Y Px Py : V →ₗ[ℂ] V)
    (hX : linearCommutator M X = 0)
    (hY : linearCommutator M Y = 0) :
    linearCommutator M (orbitalAngularMomentumZ X Y Px Py) ≠ 0 ↔
      X.comp (linearCommutator M Py) - Y.comp (linearCommutator M Px) ≠ 0 := by
  rw [linearCommutator_orbitalAngularMomentumZ_of_commutes_position M X Y Px Py hX hY]

/-- Continuum-sign specialization for `Pᵢ = -i ℏ ∂ᵢ`:
`[M_f,L_z] = X (iℏ D_y) - Y (iℏ D_x)` once the momentum commutators have been identified with
multiplication by the derivatives of the localizer. -/
theorem linearCommutator_orbitalAngularMomentumZ_continuum_sign
    (M X Y Px Py Dx Dy : V →ₗ[ℂ] V) (ℏ : ℝ)
    (hX : linearCommutator M X = 0)
    (hY : linearCommutator M Y = 0)
    (hPx : linearCommutator M Px = (Complex.I * (ℏ : ℂ)) • Dx)
    (hPy : linearCommutator M Py = (Complex.I * (ℏ : ℂ)) • Dy) :
    linearCommutator M (orbitalAngularMomentumZ X Y Px Py) =
      X.comp ((Complex.I * (ℏ : ℂ)) • Dy) -
        Y.comp ((Complex.I * (ℏ : ℂ)) • Dx) := by
  exact linearCommutator_orbitalAngularMomentumZ_of_derivative_localizers
    M X Y Px Py Dx Dy (Complex.I * (ℏ : ℂ)) hX hY hPx hPy

end ConservationLaw
