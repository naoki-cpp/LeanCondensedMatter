import LeanCondensedMatter.Analysis.Calculus.BalanceLaw
import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Symmetric localization as a balance-law realization

This module contains a representation-independent algebraic realization of localized one-body
quantities. Given a linear localization map `M` and a one-body quantity `m`, define

```text
Qₘ(f) = 1/2 {M f, m}.
```

Commutation with a supplied generator `h` splits into transport and source terms. When the
transport functional factors through differential test data, this decomposition supplies an
instance of the abstract `ConservationLaw.BalanceLaw`.

The construction is deliberately kept in `Analysis`: it is pure operator algebra and is reused by
both first quantization and second quantization. It is one realization of a balance law, not the
definition of balance itself.
-/

namespace ConservationLaw

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
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

/-- Differential factorization of bare localization transport lifts to any symmetrically localized
one-body quantity. -/
theorem factorsThroughDifferential_transport
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (J : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hJ : FactorsThroughDifferential d
      (localizationCommutatorFunctional V h M) J) :
    FactorsThroughDifferential d
      (transportFunctional V h M m)
      ((symmetrizedProductRightLinear V m).comp J) := by
  exact FactorsThroughDifferential.postcomp hJ (symmetrizedProductRightLinear V m)

/-- The symmetric-localization commutator decomposition becomes an abstract balance law whenever
the transport term has a differential current representation. -/
noncomputable def symmetricLocalizationBalanceLaw
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (J : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hJ : FactorsThroughDifferential d (transportFunctional V h M m) J) :
    BalanceLaw (commutatorEvolution h) (localizedQuantityFunctional V M m) d where
  current := J
  source := sourceFunctional V h M m
  balance := by
    intro f
    rw [commutatorEvolution_localizedQuantityFunctional V h M m f, hJ f]

end ConservationLaw
