import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeneralizedQuantity

set_option linter.style.header false

/-!
# Weak current representations of generalized transport functionals

This module continues issue #1159 by separating two notions that should not be conflated:

1. the canonical transport functional `Φ(f)` coming from the localized balance law;
2. an optional factorization of that functional through a differential-like map `d`.

Abstractly, if

```text
d : Test →ₗ[ℂ] OneForm
Φ : Test →ₗ[ℂ] Obs
J : OneForm →ₗ[ℂ] Obs
```

then `FactorsThroughDifferential d Φ J` means

```text
Φ(f) = J(d f)
```

for every test object `f`.

The name is intentionally semantic: this module does not assume that `OneForm` is literally a
space of differential forms, nor does it assert that `J` is a zeroth-order pairing with a local
vector-current density. In a continuum realization, the latter stronger statement corresponds to
the familiar physics weak form `Φ(f) = ∫ j · ∇f`; it requires additional analytic/locality data and
belongs to a downstream specialization.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

variable {Test OneForm Obs : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable [AddCommGroup Obs] [Module ℂ Obs]

/-- A transport functional `Φ` factors through a differential-like map `d` via the 1-form flux
functional `J` when `Φ(f) = J(d f)` for every test object.

This is weaker than existence of a local vector-current density: `J` may itself use derivatives or
other nonlocal information contained in its `OneForm` argument. -/
def FactorsThroughDifferential
    (d : Test →ₗ[ℂ] OneForm) (Φ : Test →ₗ[ℂ] Obs) (J : OneForm →ₗ[ℂ] Obs) : Prop :=
  ∀ f, Φ f = J (d f)

namespace FactorsThroughDifferential

/-- Factorization through `d` is equivalent to equality with the composite `J ∘ d`. -/
theorem iff_eq_comp
    {d : Test →ₗ[ℂ] OneForm} {Φ : Test →ₗ[ℂ] Obs} {J : OneForm →ₗ[ℂ] Obs} :
    FactorsThroughDifferential d Φ J ↔ Φ = J.comp d := by
  constructor
  · intro h
    apply LinearMap.ext
    intro f
    exact h f
  · intro h f
    rw [h]
    rfl

/-- A factorized transport functional vanishes on test objects annihilated by `d`. -/
theorem eq_zero_of_map_eq_zero
    {d : Test →ₗ[ℂ] OneForm} {Φ : Test →ₗ[ℂ] Obs} {J : OneForm →ₗ[ℂ] Obs}
    (h : FactorsThroughDifferential d Φ J) {f : Test} (hf : d f = 0) :
    Φ f = 0 := by
  rw [h f, hf, map_zero]

/-- Scalar multiplication preserves a differential factorization. -/
theorem smul
    {d : Test →ₗ[ℂ] OneForm} {Φ : Test →ₗ[ℂ] Obs} {J : OneForm →ₗ[ℂ] Obs}
    (h : FactorsThroughDifferential d Φ J) (c : ℂ) :
    FactorsThroughDifferential d (c • Φ) (c • J) := by
  intro f
  simp [h f]

/-- Postcomposition by a linear observable map preserves a differential factorization. -/
theorem postcomp
    {Obs' : Type*} [AddCommGroup Obs'] [Module ℂ Obs']
    {d : Test →ₗ[ℂ] OneForm} {Φ : Test →ₗ[ℂ] Obs} {J : OneForm →ₗ[ℂ] Obs}
    (h : FactorsThroughDifferential d Φ J) (L : Obs →ₗ[ℂ] Obs') :
    FactorsThroughDifferential d (L.comp Φ) (L.comp J) := by
  intro f
  simp only [LinearMap.comp_apply]
  rw [h f]

end FactorsThroughDifferential

/-- Data of one chosen flux functional representing `Φ` through `d`.

No locality or uniqueness claim is bundled into this structure. Different representatives can be
physically equivalent after quotienting by boundary/improvement terms in concrete models. -/
structure DifferentialCurrentRepresentation
    (d : Test →ₗ[ℂ] OneForm) (Φ : Test →ₗ[ℂ] Obs) where
  /-- The chosen flux functional on differential-like test data. -/
  current : OneForm →ₗ[ℂ] Obs
  /-- Proof that the canonical transport functional is represented by `current ∘ d`. -/
  factors : FactorsThroughDifferential d Φ current

namespace DifferentialCurrentRepresentation

/-- Evaluate the represented transport functional on a test object. -/
theorem apply
    {d : Test →ₗ[ℂ] OneForm} {Φ : Test →ₗ[ℂ] Obs}
    (R : DifferentialCurrentRepresentation d Φ) (f : Test) :
    Φ f = R.current (d f) :=
  R.factors f

end DifferentialCurrentRepresentation

variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- The canonical transport term packaged as a linear functional of the localization test object.

This is the linear-map form of `transportCommutator`; packaging it this way lets downstream models
state precisely that the canonical transport functional factors through a gradient/differential. -/
noncomputable def transportFunctional
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁) where
  toFun := transportCommutator 𝓗₁ h M m
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro v
    simp [transportCommutator, symmetrizedProduct, AlgebraicFock.linearCommutator]
    module
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro v
    simp [transportCommutator, symmetrizedProduct, AlgebraicFock.linearCommutator]
    module

@[simp]
theorem transportFunctional_apply
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    transportFunctional 𝓗₁ h M m f = transportCommutator 𝓗₁ h M m f :=
  rfl

/-- The bare localization commutator `f ↦ [h, M(f)]`, packaged linearly. Charge transport is a
scalar multiple of this functional. -/
noncomputable def localizationCommutatorFunctional
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) :
    Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁) where
  toFun := fun f => AlgebraicFock.linearCommutator h (M f)
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro v
    simp [AlgebraicFock.linearCommutator]
    module
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro v
    simp [AlgebraicFock.linearCommutator]
    module

@[simp]
theorem localizationCommutatorFunctional_apply
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (f : Test) :
    localizationCommutatorFunctional 𝓗₁ h M f =
      AlgebraicFock.linearCommutator h (M f) :=
  rfl

/-- For `m = q I`, the generalized transport functional is exactly `q` times the bare
localization commutator functional. -/
theorem transportFunctional_smul_id
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (q : ℂ) :
    transportFunctional 𝓗₁ h M (q • LinearMap.id) =
      q • localizationCommutatorFunctional 𝓗₁ h M := by
  apply LinearMap.ext
  intro f
  simp

/-- Any differential factorization of the bare localization commutator induces the corresponding
charge-current factorization for `m = q I`. -/
theorem factorsThroughDifferential_transport_smul_id
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (d : Test →ₗ[ℂ] OneForm)
    (J : OneForm →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (q : ℂ)
    (hJ : FactorsThroughDifferential d (localizationCommutatorFunctional 𝓗₁ h M) J) :
    FactorsThroughDifferential d (transportFunctional 𝓗₁ h M (q • LinearMap.id)) (q • J) := by
  rw [transportFunctional_smul_id]
  exact hJ.smul q

end Field
end Fermionic
end SecondQuantization
