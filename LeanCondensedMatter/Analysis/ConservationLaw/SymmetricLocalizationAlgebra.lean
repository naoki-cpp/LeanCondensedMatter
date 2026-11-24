import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct

set_option linter.style.header false

/-!
# Symmetric-localization operator algebra

This module owns the representation-neutral operator algebra shared by intrinsic and represented
symmetric-localization balance constructions. Given a linear localization map `M` and a one-body
quantity `m`, define (over a field where 2 is nonzero for the physical interpretation)

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

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K Test : Type*} [Field K]
variable [AddCommGroup Test] [Module K Test]
variable (V : Type*) [AddCommGroup V] [Module K V]

/-- A one-body quantity symmetrically localized by a linear test map. -/
noncomputable def localizedQuantityFunctional
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) :
    Test →ₗ[K] (V →ₗ[K] V) :=
  (LinearMap.symmetrizedProductRightLinear V m).comp M

@[simp]
theorem localizedQuantityFunctional_apply
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) (f : Test) :
    localizedQuantityFunctional V M m f = LinearMap.symmetrizedProduct (M f) m :=
  rfl

/-- The bare localization commutator as a linear map on tests. -/
noncomputable def localizationCommutatorFunctional
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V)) :
    Test →ₗ[K] (V →ₗ[K] V) :=
  (LieAlgebra.ad K (Module.End K V) h).comp M

@[simp]
theorem localizationCommutatorFunctional_apply
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V)) (f : Test) :
    localizationCommutatorFunctional V h M f = ⁅h, M f⁆ :=
  rfl

/-- The transport contribution to the symmetric-localization commutator. -/
noncomputable def transportFunctional
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) :
    Test →ₗ[K] (V →ₗ[K] V) :=
  (LinearMap.symmetrizedProductRightLinear V m).comp
    (localizationCommutatorFunctional V h M)

@[simp]
theorem transportFunctional_apply
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) (f : Test) :
    transportFunctional V h M m f = LinearMap.symmetrizedProduct ⁅h, M f⁆ m :=
  rfl

/-- The source/torque contribution to the symmetric-localization commutator. -/
noncomputable def sourceFunctional
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) :
    Test →ₗ[K] (V →ₗ[K] V) :=
  localizedQuantityFunctional V M ⁅h, m⁆

@[simp]
theorem sourceFunctional_apply
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) (f : Test) :
    sourceFunctional V h M m f = LinearMap.symmetrizedProduct (M f) ⁅h, m⁆ :=
  rfl

/-- The commutator is a derivation on symmetric localization, giving transport plus source. -/
theorem lie_localizedQuantity
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) (f : Test) :
    ⁅h, localizedQuantityFunctional V M m f⁆ =
      transportFunctional V h M m f + sourceFunctional V h M m f :=
  LinearMap.lie_symmetrizedProduct h (M f) m

end ConservationLaw
