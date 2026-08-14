import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ChargeDensity
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

@[simp]
theorem symmetrizedProduct_zero_left {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : V →ₗ[ℂ] V) :
    symmetrizedProduct (0 : V →ₗ[ℂ] V) A = 0 := by
  apply LinearMap.ext
  intro v
  simp [symmetrizedProduct]

@[simp]
theorem symmetrizedProduct_zero_right {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : V →ₗ[ℂ] V) :
    symmetrizedProduct A (0 : V →ₗ[ℂ] V) = 0 := by
  rw [symmetrizedProduct_comm]
  exact symmetrizedProduct_zero_left A

/-- Scalar multiples of the identity behave as scalar quantities under symmetrization. -/
@[simp]
theorem symmetrizedProduct_smul_id {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : V →ₗ[ℂ] V) (q : ℂ) :
    symmetrizedProduct A (q • LinearMap.id) = q • A := by
  apply LinearMap.ext
  intro v
  simp [symmetrizedProduct]
  module

/-- If two operators commute, their symmetrized product reduces to ordinary composition. -/
theorem symmetrizedProduct_eq_comp_of_commutes {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : V →ₗ[ℂ] V)
    (hAB : AlgebraicFock.linearCommutator A B = 0) :
    symmetrizedProduct A B = A.comp B := by
  apply LinearMap.ext
  intro v
  have hzero : A (B v) - B (A v) = 0 := by
    have h := congrArg (fun T : V →ₗ[ℂ] V => T v) hAB
    simpa [AlgebraicFock.linearCommutator] using h
  have hcomm : A (B v) = B (A v) := sub_eq_zero.mp hzero
  change (1 / 2 : ℂ) • (A (B v) + B (A v)) = A (B v)
  rw [← hcomm]
  module

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

/-- When localization commutes with the quantity, symmetric localization reduces to `M f ∘ m`. -/
theorem localizedQuantity_eq_comp_of_commutes
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test)
    (hcomm : AlgebraicFock.linearCommutator (M f) m = 0) :
    localizedQuantity 𝓗₁ M m f = (M f).comp m := by
  simpa [localizedQuantity] using
    (symmetrizedProduct_eq_comp_of_commutes (M f) m hcomm)

/-- Charge-like quantities `q I` commute with localization and reduce to scalar multiplication. -/
@[simp]
theorem localizedQuantity_smul_id
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (q : ℂ) (f : Test) :
    localizedQuantity 𝓗₁ M (q • LinearMap.id) f = q • M f := by
  simp [localizedQuantity]

/-- Canonical transport part of the commutator balance law.

This is kept as a functional of the localization test object. It is not assumed to factor through
a gradient or to admit a local vector-current density. -/
noncomputable def transportCommutator (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    𝓗₁ →ₗ[ℂ] 𝓗₁ :=
  symmetrizedProduct (AlgebraicFock.linearCommutator h (M f)) m

/-- For a charge-like quantity `q I`, the canonical transport term is `q [h, M f]`. -/
@[simp]
theorem transportCommutator_smul_id (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (q : ℂ) (f : Test) :
    transportCommutator 𝓗₁ h M (q • LinearMap.id) f =
      q • AlgebraicFock.linearCommutator h (M f) := by
  simp [transportCommutator]

/-- Canonical source/torque part of the commutator balance law. -/
noncomputable def sourceCommutator (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    𝓗₁ →ₗ[ℂ] 𝓗₁ :=
  symmetrizedProduct (M f) (AlgebraicFock.linearCommutator h m)

/-- A scalar multiple of the identity commutes with every one-particle Hamiltonian. -/
@[simp]
theorem linearCommutator_smul_id_right {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : V →ₗ[ℂ] V) (q : ℂ) :
    AlgebraicFock.linearCommutator h (q • LinearMap.id) = 0 := by
  apply LinearMap.ext
  intro v
  simp [AlgebraicFock.linearCommutator]

/-- A conserved quantity has no local source/torque contribution. -/
@[simp]
theorem sourceCommutator_eq_zero_of_commutes (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test)
    (hm : AlgebraicFock.linearCommutator h m = 0) :
    sourceCommutator 𝓗₁ h M m f = 0 := by
  simp [sourceCommutator, hm]

/-- Charge-like quantities `q I` have no source/torque term. -/
theorem sourceCommutator_smul_id (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (q : ℂ) (f : Test) :
    sourceCommutator 𝓗₁ h M (q • LinearMap.id) f = 0 := by
  apply sourceCommutator_eq_zero_of_commutes 𝓗₁ h M (q • LinearMap.id) f
  exact linearCommutator_smul_id_right h q

/-- Purely algebraic balance decomposition for a generalized localized one-body quantity. -/
theorem linearCommutator_localizedQuantity (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    AlgebraicFock.linearCommutator h (localizedQuantity 𝓗₁ M m f) =
      transportCommutator 𝓗₁ h M m f + sourceCommutator 𝓗₁ h M m f := by
  simpa [localizedQuantity, transportCommutator, sourceCommutator] using
    linearCommutator_symmetrizedProduct h (M f) m

/-- For a conserved quantity, the localized balance law contains only the transport term. -/
theorem linearCommutator_localizedQuantity_of_commutes (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test)
    (hm : AlgebraicFock.linearCommutator h m = 0) :
    AlgebraicFock.linearCommutator h (localizedQuantity 𝓗₁ M m f) =
      transportCommutator 𝓗₁ h M m f := by
  rw [linearCommutator_localizedQuantity]
  simp [sourceCommutator, hm]

/-- The total many-body observable associated with a one-particle quantity `m`. -/
noncomputable def oneBodyObservable (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  AlgebraicFock.dGamma 𝓗₁ m

/-- Charge-like total observables are scalar multiples of the algebraic number operator. -/
theorem oneBodyObservable_smul_id (q : ℂ) :
    oneBodyObservable 𝓗₁ (q • LinearMap.id) =
      q • AlgebraicFock.numberOperator 𝓗₁ := by
  rw [oneBodyObservable, AlgebraicFock.dGamma_smul, AlgebraicFock.numberOperator]

/-- Many-body lift of a generalized localized quantity. -/
noncomputable def manyBodyLocalizedQuantity (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  AlgebraicFock.dGamma 𝓗₁ (localizedQuantity 𝓗₁ M m f)

/-- The generalized localized many-body quantity recovers the existing charge-density API for
`m = q I`. -/
theorem manyBodyLocalizedQuantity_smul_id
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (q : ℂ) (f : Test) :
    manyBodyLocalizedQuantity 𝓗₁ M (q • LinearMap.id) f =
      chargeDensity 𝓗₁ q M f := by
  calc
    manyBodyLocalizedQuantity 𝓗₁ M (q • LinearMap.id) f =
        AlgebraicFock.dGamma 𝓗₁ (q • M f) := by
      rw [manyBodyLocalizedQuantity, localizedQuantity_smul_id]
    _ = q • AlgebraicFock.dGamma 𝓗₁ (M f) :=
      AlgebraicFock.dGamma_smul 𝓗₁ q (M f)
    _ = chargeDensity 𝓗₁ q M f := by
      symm
      exact chargeDensity_apply 𝓗₁ q M f

/-- Second quantization preserves the generalized balance decomposition. -/
theorem dGamma_commutator_manyBodyLocalizedQuantity (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    AlgebraicFock.linearCommutator
        (AlgebraicFock.dGamma 𝓗₁ h) (manyBodyLocalizedQuantity 𝓗₁ M m f) =
      AlgebraicFock.dGamma 𝓗₁ (transportCommutator 𝓗₁ h M m f) +
        AlgebraicFock.dGamma 𝓗₁ (sourceCommutator 𝓗₁ h M m f) := by
  rw [manyBodyLocalizedQuantity, AlgebraicFock.dGamma_linearCommutator]
  rw [linearCommutator_localizedQuantity, AlgebraicFock.dGamma_add]

/-- The charge specialization of the generalized many-body balance path agrees exactly with the
pre-existing charge-density commutator theorem. -/
theorem dGamma_commutator_manyBodyLocalizedQuantity_smul_id
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁) (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (q : ℂ) (f : Test) :
    AlgebraicFock.linearCommutator
        (AlgebraicFock.dGamma 𝓗₁ h)
        (manyBodyLocalizedQuantity 𝓗₁ M (q • LinearMap.id) f) =
      q • AlgebraicFock.dGamma 𝓗₁ (AlgebraicFock.linearCommutator h (M f)) := by
  rw [manyBodyLocalizedQuantity_smul_id]
  exact dGamma_commutator_chargeDensity 𝓗₁ q M h f

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
