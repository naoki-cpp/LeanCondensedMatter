import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationCommutator
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Generalized one-body quantities and algebraic balance laws

This module starts issue #1159 from the representation-independent algebraic layer.

For a one-particle quantity `m` and a localization observable `M f`, the symmetrically localized
quantity is

```text
ρₘ(f) = 1/2 {M f, m}.
```

No assumption is made that `m` is an internal degree of freedom or that it commutes with
localization. The commutator with a one-particle Hamiltonian splits canonically into a transport
part and a source/torque part:

```text
[h, ρₘ(f)]
  = 1/2 {[h, M f], m}
  + 1/2 {M f, [h, m]}.
```

A local vector-current representation of the transport term is deliberately *not* chosen here.
Such a representation requires extra locality hypotheses and belongs to downstream continuum or
lattice specializations.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

variable {Test : Type*} [AddCommGroup Test] [Module ℂ Test]
variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- Symmetrized composition `1/2 {A, B}` of two complex-linear endomorphisms.

At this purely algebraic layer this records the operator expression only; self-adjointness belongs
to Hilbert-space specializations carrying the required star/adjoint structure. -/
noncomputable def symmetrizedProduct {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  (1 / 2 : ℂ) • (A.comp B + B.comp A)

@[simp]
theorem symmetrizedProduct_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : V →ₗ[ℂ] V) (v : V) :
    symmetrizedProduct A B v = (1 / 2 : ℂ) • (A (B v) + B (A v)) := by
  rfl

/-- The symmetrized product is symmetric in its two arguments. -/
theorem symmetrizedProduct_comm {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : V →ₗ[ℂ] V) :
    symmetrizedProduct A B = symmetrizedProduct B A := by
  apply LinearMap.ext
  intro v
  simp [symmetrizedProduct, add_comm]

/-- The commutator acts as a derivation on the symmetrized product. -/
theorem linearCommutator_symmetrizedProduct {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h A B : V →ₗ[ℂ] V) :
    AlgebraicFock.linearCommutator h (symmetrizedProduct A B) =
      symmetrizedProduct (AlgebraicFock.linearCommutator h A) B +
        symmetrizedProduct A (AlgebraicFock.linearCommutator h B) := by
  apply LinearMap.ext
  intro v
  simp [AlgebraicFock.linearCommutator, symmetrizedProduct]
  module

/-- A one-particle quantity localized by the observable `M f`.

The symmetrization is essential when localization does not commute with the quantity operator, as
can happen for spatial, differential, or nonlocal quantities such as orbital angular momentum. -/
noncomputable def localizedQuantity (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) : 𝓗₁ →ₗ[ℂ] 𝓗₁ :=
  symmetrizedProduct (M f) m

/-- Canonical transport part of the commutator balance law.

This is kept as a functional of the localization test object. It is not assumed to factor through
a gradient or to admit a local vector-current density. -/
noncomputable def transportCommutator (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    𝓗₁ →ₗ[ℂ] 𝓗₁ :=
  symmetrizedProduct (AlgebraicFock.linearCommutator h (M f)) m

/-- Canonical source/torque part of the commutator balance law. -/
noncomputable def sourceCommutator (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    𝓗₁ →ₗ[ℂ] 𝓗₁ :=
  symmetrizedProduct (M f) (AlgebraicFock.linearCommutator h m)

/-- Purely algebraic balance decomposition for a generalized localized one-body quantity. -/
theorem linearCommutator_localizedQuantity (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    AlgebraicFock.linearCommutator h (localizedQuantity 𝓗₁ M m f) =
      transportCommutator 𝓗₁ h M m f + sourceCommutator 𝓗₁ h M m f := by
  simpa [localizedQuantity, transportCommutator, sourceCommutator] using
    linearCommutator_symmetrizedProduct h (M f) m

/-- The total many-body observable associated with a one-particle quantity `m`. -/
noncomputable def oneBodyObservable (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  AlgebraicFock.dGamma 𝓗₁ m

/-- Many-body lift of a generalized localized quantity. -/
noncomputable def manyBodyLocalizedQuantity (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  AlgebraicFock.dGamma 𝓗₁ (localizedQuantity 𝓗₁ M m f)

/-- Second quantization preserves the generalized balance decomposition. -/
theorem dGamma_commutator_manyBodyLocalizedQuantity (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    AlgebraicFock.linearCommutator
        (AlgebraicFock.dGamma 𝓗₁ h) (manyBodyLocalizedQuantity 𝓗₁ M m f) =
      AlgebraicFock.dGamma 𝓗₁ (transportCommutator 𝓗₁ h M m f) +
        AlgebraicFock.dGamma 𝓗₁ (sourceCommutator 𝓗₁ h M m f) := by
  rw [manyBodyLocalizedQuantity, AlgebraicFock.dGamma_linearCommutator]
  rw [linearCommutator_localizedQuantity, AlgebraicFock.dGamma_add]

/-- A vanishing one-particle commutator gives conservation of the corresponding total many-body
quantity. This is a global statement only; no local-current representation is inferred. -/
theorem oneBodyObservable_commutes_of_commutes (h m : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (hm : AlgebraicFock.linearCommutator h m = 0) :
    AlgebraicFock.linearCommutator
        (AlgebraicFock.dGamma 𝓗₁ h) (oneBodyObservable 𝓗₁ m) = 0 := by
  rw [oneBodyObservable, AlgebraicFock.dGamma_linearCommutator, hm,
    AlgebraicFock.dGamma_zero]

end Field
end Fermionic
end SecondQuantization
