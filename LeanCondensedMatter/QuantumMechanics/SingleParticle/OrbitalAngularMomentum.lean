import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Single-particle orbital angular momentum in arbitrary directions

For complexified spatial directions `u` and `v`, with direction-linear position
and momentum operators `X` and `P`, define the alternating orbital quantity

```text
L(u,v) = X(u) P(v) - X(v) P(u).
```

This is an oriented-plane (bivector) component, requiring neither preferred
Cartesian axes nor a metric or orientation identifying bivectors with axial
vectors. For a chosen positively oriented Cartesian frame, `L(eₓ,eᵧ)` is the
usual `L_z`. The construction is natural under linear changes of directions.

When a localizer `M` commutes with both position components, its commutator
with `L(u,v)` depends only on the momentum-localizer commutators. Thus a
continuum orbital quantity does not automatically satisfy the commutation
hypothesis of the conventional localized-current theorem.

The operators are complex-linear endomorphisms on a shared invariant algebraic
domain. No unbounded-operator or second-quantization structure is assumed.
-/

namespace QuantumMechanics
namespace SingleParticle

attribute [local instance 100] LieRing.ofAssociativeRing

variable {E V : Type*}
variable [AddCommGroup E] [Module ℂ E]
variable [AddCommGroup V] [Module ℂ V]

/-- The oriented-plane orbital-angular-momentum component
`L(u,v) = X(u) P(v) - X(v) P(u)`.

`E` models complexified spatial directions; concrete continuum models can
supply position and momentum maps on a common invariant test-function space. -/
noncomputable def orbitalAngularMomentum
    (X P : E →ₗ[ℂ] (V →ₗ[ℂ] V)) (u v : E) : V →ₗ[ℂ] V :=
  (X u).comp (P v) - (X v).comp (P u)

/-- Orbital angular momentum vanishes on two equal directions. -/
@[simp] theorem orbitalAngularMomentum_self
    (X P : E →ₗ[ℂ] (V →ₗ[ℂ] V)) (u : E) :
    orbitalAngularMomentum X P u u = 0 := by
  simp [orbitalAngularMomentum]

/-- Reversing the orientation of a plane reverses its orbital component. -/
theorem orbitalAngularMomentum_swap
    (X P : E →ₗ[ℂ] (V →ₗ[ℂ] V)) (u v : E) :
    orbitalAngularMomentum X P v u = -orbitalAngularMomentum X P u v := by
  unfold orbitalAngularMomentum
  module

/-- The orbital component is natural under any linear reparametrization of
directions; it therefore does not depend on a chosen coordinate frame. -/
theorem orbitalAngularMomentum_comp
    {F : Type*} [AddCommGroup F] [Module ℂ F]
    (X P : E →ₗ[ℂ] (V →ₗ[ℂ] V)) (T : F →ₗ[ℂ] E) (u v : F) :
    orbitalAngularMomentum (X.comp T) (P.comp T) u v =
      orbitalAngularMomentum X P (T u) (T v) := by
  rfl

/-- Product expansion of a localization commutator with orbital angular momentum
in an arbitrary oriented plane. -/
theorem lie_orbitalAngularMomentum
    (M : V →ₗ[ℂ] V) (X P : E →ₗ[ℂ] (V →ₗ[ℂ] V)) (u v : E) :
    ⁅M, orbitalAngularMomentum X P u v⁆ =
      ((⁅M, X u⁆).comp (P v) + (X u).comp (⁅M, P v⁆)) -
        ((⁅M, X v⁆).comp (P u) + (X v).comp (⁅M, P u⁆)) := by
  ext w
  simp [orbitalAngularMomentum, LieRing.of_associative_ring_bracket,
    Module.End.mul_eq_comp]
  module

/-- When localization commutes with positions in the two directions,
only the momentum-localization commutators remain. -/
theorem lie_orbitalAngularMomentum_of_commutes_position
    (M : V →ₗ[ℂ] V) (X P : E →ₗ[ℂ] (V →ₗ[ℂ] V)) (u v : E)
    (hXu : ⁅M, X u⁆ = 0) (hXv : ⁅M, X v⁆ = 0) :
    ⁅M, orbitalAngularMomentum X P u v⁆ =
      (X u).comp (⁅M, P v⁆) - (X v).comp (⁅M, P u⁆) := by
  rw [lie_orbitalAngularMomentum, hXu, hXv]
  simp

/-- Supplied directional derivative-localizers `Du` and `Dv`
represent the momentum-localization commutators with a common coefficient `c`. -/
theorem lie_orbitalAngularMomentum_of_derivative_localizers
    (M : V →ₗ[ℂ] V) (X P : E →ₗ[ℂ] (V →ₗ[ℂ] V)) (u v : E)
    (Du Dv : V →ₗ[ℂ] V) (c : ℂ)
    (hXu : ⁅M, X u⁆ = 0) (hXv : ⁅M, X v⁆ = 0)
    (hPu : ⁅M, P u⁆ = c • Du) (hPv : ⁅M, P v⁆ = c • Dv) :
    ⁅M, orbitalAngularMomentum X P u v⁆ =
      (X u).comp (c • Dv) - (X v).comp (c • Du) := by
  rw [lie_orbitalAngularMomentum_of_commutes_position M X P u v hXu hXv,
    hPu, hPv]

/-- Exact obstruction to localizer commutation in an arbitrary oriented plane. -/
theorem lie_orbitalAngularMomentum_ne_zero_iff
    (M : V →ₗ[ℂ] V) (X P : E →ₗ[ℂ] (V →ₗ[ℂ] V)) (u v : E)
    (hXu : ⁅M, X u⁆ = 0) (hXv : ⁅M, X v⁆ = 0) :
    ⁅M, orbitalAngularMomentum X P u v⁆ ≠ 0 ↔
      (X u).comp (⁅M, P v⁆) - (X v).comp (⁅M, P u⁆) ≠ 0 := by
  rw [lie_orbitalAngularMomentum_of_commutes_position M X P u v hXu hXv]

/-- Continuum-sign specialization `P(w) = -i ℏ ∂_w`. The assumptions
identify the supplied directional localizer derivatives with the
momentum-localization commutators; no analytic domain result is asserted. -/
theorem lie_orbitalAngularMomentum_continuum_sign
    (M : V →ₗ[ℂ] V) (X P : E →ₗ[ℂ] (V →ₗ[ℂ] V)) (u v : E)
    (Du Dv : V →ₗ[ℂ] V) (ℏ : ℝ)
    (hXu : ⁅M, X u⁆ = 0) (hXv : ⁅M, X v⁆ = 0)
    (hPu : ⁅M, P u⁆ = (Complex.I * (ℏ : ℂ)) • Du)
    (hPv : ⁅M, P v⁆ = (Complex.I * (ℏ : ℂ)) • Dv) :
    ⁅M, orbitalAngularMomentum X P u v⁆ =
      (X u).comp ((Complex.I * (ℏ : ℂ)) • Dv) -
        (X v).comp ((Complex.I * (ℏ : ℂ)) • Du) := by
  exact lie_orbitalAngularMomentum_of_derivative_localizers
    M X P u v Du Dv (Complex.I * (ℏ : ℂ)) hXu hXv hPu hPv

end SingleParticle
end QuantumMechanics
