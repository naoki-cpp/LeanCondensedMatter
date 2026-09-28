import Mathlib.Algebra.Lie.OfAssociative

set_option linter.style.header false

/-!
# Single-particle orbital-angular-momentum commutators

This module records the one-particle operator algebra needed to distinguish continuum-like orbital
angular momentum from an internal degree of freedom.

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

No unbounded-operator or second-quantization structure is used here. Generic commutator product and
additivity rules come from Mathlib's associative Lie bracket; this module owns
the orbital-angular-momentum interpretation and continuum-sign specialization.
-/

namespace QuantumMechanics
namespace SingleParticle

attribute [local instance 100] LieRing.ofAssociativeRing

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Algebraic `z` component of orbital angular momentum, `L_z = X Pᵧ - Y Pₓ`.

The inputs are deliberately only complex-linear endomorphisms. Concrete continuum models may later
instantiate them with position and momentum operators on a common invariant test-function space. -/
noncomputable def orbitalAngularMomentumZ
    (X Y Px Py : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  X.comp Py - Y.comp Px

/-- Expansion of a localization commutator with algebraic orbital angular momentum. -/
theorem lie_orbitalAngularMomentumZ
    (M X Y Px Py : V →ₗ[ℂ] V) :
    ⁅M, orbitalAngularMomentumZ X Y Px Py⁆ =
      ((⁅M, X⁆).comp Py + X.comp (⁅M, Py⁆)) -
        ((⁅M, Y⁆).comp Px + Y.comp (⁅M, Px⁆)) := by
  simp only [orbitalAngularMomentumZ, ← Module.End.mul_eq_comp]
  rw [lie_sub, leibniz_lie, leibniz_lie]

/-- If localization commutes with position, its orbital commutator is controlled entirely by the
momentum-localization commutators:

`[M,L_z] = X [M,Pᵧ] - Y [M,Pₓ]`.
-/
theorem lie_orbitalAngularMomentumZ_of_commutes_position
    (M X Y Px Py : V →ₗ[ℂ] V)
    (hX : ⁅M, X⁆ = 0)
    (hY : ⁅M, Y⁆ = 0) :
    ⁅M, orbitalAngularMomentumZ X Y Px Py⁆ =
      X.comp (⁅M, Py⁆) - Y.comp (⁅M, Px⁆) := by
  rw [lie_orbitalAngularMomentumZ, hX, hY]
  simp

/-- Specialization when the momentum-localization commutators are represented by supplied
"derivative localizer" operators `Dx` and `Dy` with a common scalar coefficient `c`.

For continuum momentum `Pᵢ = -i ℏ ∂ᵢ`, the physical coefficient is `c = i ℏ` and `Di` is
multiplication by `∂ᵢ f`. -/
theorem lie_orbitalAngularMomentumZ_of_derivative_localizers
    (M X Y Px Py Dx Dy : V →ₗ[ℂ] V) (c : ℂ)
    (hX : ⁅M, X⁆ = 0)
    (hY : ⁅M, Y⁆ = 0)
    (hPx : ⁅M, Px⁆ = c • Dx)
    (hPy : ⁅M, Py⁆ = c • Dy) :
    ⁅M, orbitalAngularMomentumZ X Y Px Py⁆ =
      X.comp (c • Dy) - Y.comp (c • Dx) := by
  rw [lie_orbitalAngularMomentumZ_of_commutes_position M X Y Px Py hX hY,
    hPx, hPy]

/-- Exact nonvanishing criterion under position-localizer commutation.

This makes the obstruction explicit: continuum-like `L_z` fails to commute with localization exactly
when the derivative-localization combination on the right is nonzero. -/
theorem lie_orbitalAngularMomentumZ_ne_zero_iff
    (M X Y Px Py : V →ₗ[ℂ] V)
    (hX : ⁅M, X⁆ = 0)
    (hY : ⁅M, Y⁆ = 0) :
    ⁅M, orbitalAngularMomentumZ X Y Px Py⁆ ≠ 0 ↔
      X.comp (⁅M, Py⁆) - Y.comp (⁅M, Px⁆) ≠ 0 := by
  rw [lie_orbitalAngularMomentumZ_of_commutes_position M X Y Px Py hX hY]

/-- Continuum-sign specialization for `Pᵢ = -i ℏ ∂ᵢ`:
`[M_f,L_z] = X (iℏ D_y) - Y (iℏ D_x)` once the momentum commutators have been identified with
multiplication by the derivatives of the localizer. -/
theorem lie_orbitalAngularMomentumZ_continuum_sign
    (M X Y Px Py Dx Dy : V →ₗ[ℂ] V) (ℏ : ℝ)
    (hX : ⁅M, X⁆ = 0)
    (hY : ⁅M, Y⁆ = 0)
    (hPx : ⁅M, Px⁆ = (Complex.I * (ℏ : ℂ)) • Dx)
    (hPy : ⁅M, Py⁆ = (Complex.I * (ℏ : ℂ)) • Dy) :
    ⁅M, orbitalAngularMomentumZ X Y Px Py⁆ =
      X.comp ((Complex.I * (ℏ : ℂ)) • Dy) -
        Y.comp ((Complex.I * (ℏ : ℂ)) • Dx) := by
  exact lie_orbitalAngularMomentumZ_of_derivative_localizers
    M X Y Px Py Dx Dy (Complex.I * (ℏ : ℂ)) hX hY hPx hPy

end SingleParticle
end QuantumMechanics
