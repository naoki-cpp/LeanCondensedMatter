import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Symmetric-localization operator algebra

This module owns the representation-neutral operator algebra shared by intrinsic and represented
symmetric-localization balance constructions. Given a linear localization map `M` and a one-body
quantity `m`, define

```text
Qₘ(f) = 1/2 {M f, m}.
```

Commutation with a supplied generator `h` splits into transport and source terms. This file stops
at that shared decomposition and deliberately does not choose either intrinsic or represented
balance-law packaging.

The construction is kept in `Analysis`: it is pure operator algebra reused by both intrinsic and
represented balance constructions, first quantization, and second quantization.
-/

namespace ConservationLaw

variable {Test : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Symmetrization with a fixed right-hand quantity is linear in the left operator. -/
noncomputable def symmetrizedProductRightLinear
    (m : V →ₗ[ℂ] V) :
    (V →ₗ[ℂ] V) →ₗ[ℂ] (V →ₗ[ℂ] V) where
  toFun := fun A => symmetrizedProduct A m
  map_add' := by
    intro A B
    apply LinearMap.ext
    intro v
    simp [symmetrizedProduct]
    module
  map_smul' := by
    intro c A
    apply LinearMap.ext
    intro v
    simp [symmetrizedProduct]
    module

@[simp]
theorem symmetrizedProductRightLinear_apply
    (m A : V →ₗ[ℂ] V) :
    symmetrizedProductRightLinear V m A = symmetrizedProduct A m :=
  rfl

/-- Symmetrization with a fixed left-hand operator is linear in the transported quantity. -/
noncomputable def symmetrizedProductLeftLinear
    (A : V →ₗ[ℂ] V) :
    (V →ₗ[ℂ] V) →ₗ[ℂ] (V →ₗ[ℂ] V) where
  toFun := fun m => symmetrizedProduct A m
  map_add' := by
    intro m n
    rw [symmetrizedProduct_comm A (m + n),
      symmetrizedProductRightLinear_apply,
      map_add,
      ← symmetrizedProductRightLinear_apply,
      ← symmetrizedProductRightLinear_apply]
    rw [symmetrizedProduct_comm m A, symmetrizedProduct_comm n A]
  map_smul' := by
    intro c m
    rw [symmetrizedProduct_comm A (c • m),
      symmetrizedProductRightLinear_apply,
      map_smul,
      ← symmetrizedProductRightLinear_apply]
    rw [symmetrizedProduct_comm m A]

@[simp]
theorem symmetrizedProductLeftLinear_apply
    (A m : V →ₗ[ℂ] V) :
    symmetrizedProductLeftLinear V A m = symmetrizedProduct A m :=
  rfl

/-- A one-body quantity localized by the supplied operator-valued test map `M`. -/
noncomputable def localizedQuantity
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) : V →ₗ[ℂ] V :=
  symmetrizedProduct (M f) m

/-- Symmetric localization packaged linearly in the test object. -/
noncomputable def localizedQuantityFunctional
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  (symmetrizedProductRightLinear V m).comp M

@[simp]
theorem localizedQuantityFunctional_apply
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) :
    localizedQuantityFunctional V M m f = localizedQuantity V M m f :=
  rfl

/-- When localization commutes with the quantity, symmetric localization reduces to `M f ∘ m`. -/
theorem localizedQuantity_eq_comp_of_commutes
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test)
    (hcomm : linearCommutator (M f) m = 0) :
    localizedQuantity V M m f = (M f).comp m := by
  simpa [localizedQuantity] using
    (symmetrizedProduct_eq_comp_of_commutes (M f) m hcomm)

/-- Charge-like quantities `q I` reduce to scalar multiplication under symmetric localization. -/
@[simp]
theorem localizedQuantity_smul_id
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (q : ℂ) (f : Test) :
    localizedQuantity V M (q • LinearMap.id) f = q • M f := by
  simp [localizedQuantity]

/-- The bare localization commutator `f ↦ [h,M(f)]`, packaged linearly. -/
noncomputable def localizationCommutatorFunctional
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  (commutatorEvolution h).comp M

@[simp]
theorem localizationCommutatorFunctional_apply
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (f : Test) :
    localizationCommutatorFunctional V h M f = linearCommutator h (M f) :=
  rfl

/-- Canonical transport part of the symmetric-localization commutator identity. -/
noncomputable def transportCommutator
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) : V →ₗ[ℂ] V :=
  symmetrizedProduct (linearCommutator h (M f)) m

/-- The transport contribution packaged linearly in the test object. -/
noncomputable def transportFunctional
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  (symmetrizedProductRightLinear V m).comp
    (localizationCommutatorFunctional V h M)

@[simp]
theorem transportFunctional_apply
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) :
    transportFunctional V h M m f = transportCommutator V h M m f :=
  rfl

/-- Canonical source/torque part of the symmetric-localization commutator identity. -/
noncomputable def sourceCommutator
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) : V →ₗ[ℂ] V :=
  symmetrizedProduct (M f) (linearCommutator h m)

/-- The source/torque contribution packaged linearly in the test object. -/
noncomputable def sourceFunctional
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  (symmetrizedProductRightLinear V (linearCommutator h m)).comp M

@[simp]
theorem sourceFunctional_apply
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) :
    sourceFunctional V h M m f = sourceCommutator V h M m f :=
  rfl

/-- The commutator is a derivation on symmetric localization, giving transport plus source. -/
theorem linearCommutator_localizedQuantity
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) :
    linearCommutator h (localizedQuantity V M m f) =
      transportCommutator V h M m f + sourceCommutator V h M m f := by
  simpa [localizedQuantity, transportCommutator, sourceCommutator] using
    linearCommutator_symmetrizedProduct h (M f) m

/-- The packaged localized quantity satisfies the same transport/source decomposition. -/
theorem commutatorEvolution_localizedQuantityFunctional
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) :
    commutatorEvolution h (localizedQuantityFunctional V M m f) =
      transportFunctional V h M m f + sourceFunctional V h M m f := by
  simpa using linearCommutator_localizedQuantity V h M m f

/-- A conserved one-body quantity has no local source/torque contribution. -/
@[simp]
theorem sourceCommutator_eq_zero_of_commutes
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test)
    (hm : linearCommutator h m = 0) :
    sourceCommutator V h M m f = 0 := by
  simp [sourceCommutator, hm]

/-- For a conserved quantity, the localized balance identity contains only transport. -/
theorem linearCommutator_localizedQuantity_of_commutes
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test)
    (hm : linearCommutator h m = 0) :
    linearCommutator h (localizedQuantity V M m f) =
      transportCommutator V h M m f := by
  rw [linearCommutator_localizedQuantity]
  simp [sourceCommutator, hm]

/-- Charge-like quantities have transport `q [h,M(f)]`. -/
@[simp]
theorem transportCommutator_smul_id
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (q : ℂ) (f : Test) :
    transportCommutator V h M (q • LinearMap.id) f =
      q • linearCommutator h (M f) := by
  simp [transportCommutator]

/-- Charge-like quantities have no source/torque term. -/
theorem sourceCommutator_smul_id
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (q : ℂ) (f : Test) :
    sourceCommutator V h M (q • LinearMap.id) f = 0 := by
  apply sourceCommutator_eq_zero_of_commutes V h M (q • LinearMap.id) f
  exact linearCommutator_smul_id_right h q

/-- For `m = q I`, the transport functional is `q` times the bare localization commutator. -/
theorem transportFunctional_smul_id
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (q : ℂ) :
    transportFunctional V h M (q • LinearMap.id) =
      q • localizationCommutatorFunctional V h M := by
  apply LinearMap.ext
  intro f
  simp [transportFunctional, localizationCommutatorFunctional]

end ConservationLaw
