import LeanCondensedMatter.Analysis.Operator.LinearCommutator
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Generalized one-body localized balance laws

This module owns the representation-independent algebra behind generalized local transport.
For a one-body quantity `m` and a localization observable `M f`, define

```text
ρₘ(f) = 1/2 {M f, m}.
```

Its Hamiltonian commutator splits canonically as

```text
[h, ρₘ(f)]
  = 1/2 {[h, M f], m}
  + 1/2 {M f, [h, m]}.
```

The first term is the canonical transport contribution and the second is the source/torque
contribution. No current-density representation, Hilbert-space completion, particle statistics, or
second-quantization construction is assumed here.
-/

namespace ConservationLaw

variable {Test : Type*} [AddCommGroup Test] [Module ℂ Test]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Symmetrized composition `1/2 {A, B}` of two complex-linear endomorphisms. -/
noncomputable def symmetrizedProduct {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A B : W →ₗ[ℂ] W) : W →ₗ[ℂ] W :=
  (1 / 2 : ℂ) • (A.comp B + B.comp A)

@[simp]
theorem symmetrizedProduct_apply {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A B : W →ₗ[ℂ] W) (v : W) :
    symmetrizedProduct A B v = (1 / 2 : ℂ) • (A (B v) + B (A v)) := by
  rfl

/-- The symmetrized product is symmetric in its two arguments. -/
theorem symmetrizedProduct_comm {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A B : W →ₗ[ℂ] W) :
    symmetrizedProduct A B = symmetrizedProduct B A := by
  apply LinearMap.ext
  intro v
  simp [symmetrizedProduct, add_comm]

@[simp]
theorem symmetrizedProduct_zero_left {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : W →ₗ[ℂ] W) :
    symmetrizedProduct (0 : W →ₗ[ℂ] W) A = 0 := by
  apply LinearMap.ext
  intro v
  simp [symmetrizedProduct]

@[simp]
theorem symmetrizedProduct_zero_right {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : W →ₗ[ℂ] W) :
    symmetrizedProduct A (0 : W →ₗ[ℂ] W) = 0 := by
  rw [symmetrizedProduct_comm]
  exact symmetrizedProduct_zero_left A

/-- Scalar multiples of the identity behave as scalar quantities under symmetrization. -/
@[simp]
theorem symmetrizedProduct_smul_id {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : W →ₗ[ℂ] W) (q : ℂ) :
    symmetrizedProduct A (q • LinearMap.id) = q • A := by
  apply LinearMap.ext
  intro v
  simp [symmetrizedProduct]
  module

/-- If two operators commute, their symmetrized product reduces to ordinary composition. -/
theorem symmetrizedProduct_eq_comp_of_commutes {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A B : W →ₗ[ℂ] W)
    (hAB : linearCommutator A B = 0) :
    symmetrizedProduct A B = A.comp B := by
  apply LinearMap.ext
  intro v
  have hzero : A (B v) - B (A v) = 0 := by
    have h := congrArg (fun T : W →ₗ[ℂ] W => T v) hAB
    simpa [linearCommutator] using h
  have hcomm : A (B v) = B (A v) := sub_eq_zero.mp hzero
  change (1 / 2 : ℂ) • (A (B v) + B (A v)) = A (B v)
  rw [← hcomm]
  module

/-- The commutator acts as a derivation on the symmetrized product. -/
theorem linearCommutator_symmetrizedProduct {W : Type*} [AddCommGroup W] [Module ℂ W]
    (h A B : W →ₗ[ℂ] W) :
    linearCommutator h (symmetrizedProduct A B) =
      symmetrizedProduct (linearCommutator h A) B +
        symmetrizedProduct A (linearCommutator h B) := by
  apply LinearMap.ext
  intro v
  simp [linearCommutator, symmetrizedProduct]
  module

/-- A one-body quantity localized by the observable `M f`. -/
noncomputable def localizedQuantity (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) : V →ₗ[ℂ] V :=
  symmetrizedProduct (M f) m

/-- When localization commutes with the quantity, symmetric localization reduces to `M f ∘ m`. -/
theorem localizedQuantity_eq_comp_of_commutes
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test)
    (hcomm : linearCommutator (M f) m = 0) :
    localizedQuantity V M m f = (M f).comp m := by
  simpa [localizedQuantity] using
    (symmetrizedProduct_eq_comp_of_commutes (M f) m hcomm)

/-- Charge-like quantities `q I` commute with localization and reduce to scalar multiplication. -/
@[simp]
theorem localizedQuantity_smul_id
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (q : ℂ) (f : Test) :
    localizedQuantity V M (q • LinearMap.id) f = q • M f := by
  simp [localizedQuantity]

/-- Canonical transport part of the localized commutator balance law. -/
noncomputable def transportCommutator (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test) :
    V →ₗ[ℂ] V :=
  symmetrizedProduct (linearCommutator h (M f)) m

/-- For a charge-like quantity `q I`, the canonical transport term is `q [h, M f]`. -/
@[simp]
theorem transportCommutator_smul_id (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (q : ℂ) (f : Test) :
    transportCommutator V h M (q • LinearMap.id) f =
      q • linearCommutator h (M f) := by
  simp [transportCommutator]

/-- Canonical source/torque part of the localized commutator balance law. -/
noncomputable def sourceCommutator (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test) :
    V →ₗ[ℂ] V :=
  symmetrizedProduct (M f) (linearCommutator h m)

/-- A conserved quantity has no local source/torque contribution. -/
@[simp]
theorem sourceCommutator_eq_zero_of_commutes (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test)
    (hm : linearCommutator h m = 0) :
    sourceCommutator V h M m f = 0 := by
  simp [sourceCommutator, hm]

/-- Charge-like quantities `q I` have no source/torque term. -/
theorem sourceCommutator_smul_id (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (q : ℂ) (f : Test) :
    sourceCommutator V h M (q • LinearMap.id) f = 0 := by
  apply sourceCommutator_eq_zero_of_commutes V h M (q • LinearMap.id) f
  exact linearCommutator_smul_id_right h q

/-- Purely algebraic balance decomposition for a generalized localized one-body quantity. -/
theorem linearCommutator_localizedQuantity (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test) :
    linearCommutator h (localizedQuantity V M m f) =
      transportCommutator V h M m f + sourceCommutator V h M m f := by
  simpa [localizedQuantity, transportCommutator, sourceCommutator] using
    linearCommutator_symmetrizedProduct h (M f) m

/-- For a conserved quantity, the localized balance law contains only the transport term. -/
theorem linearCommutator_localizedQuantity_of_commutes (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test)
    (hm : linearCommutator h m = 0) :
    linearCommutator h (localizedQuantity V M m f) =
      transportCommutator V h M m f := by
  rw [linearCommutator_localizedQuantity]
  simp [sourceCommutator, hm]

end ConservationLaw
