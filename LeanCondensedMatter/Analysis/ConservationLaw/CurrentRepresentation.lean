import LeanCondensedMatter.Analysis.ConservationLaw.DifferentialDependence
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak current representations

This module contains representation-specific infrastructure for weak transport functionals.
The representation-independent predicate `DependsOnlyOnDifferential` is owned by
`DifferentialDependence`.

For a linear differential-like map

```text
d : Test →ₗ[𝕜] OneForm
```

and a transport functional

```text
Φ : Test →ₗ[𝕜] Obs,
```

`IsDifferentialCurrent d Φ J` records a chosen linear current extension with
`Φ(f) = J(d f)`. A strictly stronger `LocalCurrentDensityRepresentation` chooses a current
density `j` and a supplied bilinear pairing such that `Φ(f) = pairing j (d f)`.

The pairing is deliberately abstract. Concrete continuum models may realize it by a zeroth-order
pairing such as `∫ α · j`, while lattice models may use a finite bond pairing. No locality claim is
made merely from factorization through `d`.
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs CurrentDensity : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]
variable [AddCommMonoid CurrentDensity] [Module 𝕜 CurrentDensity]

/-- `J` is a differential current representing the transport functional `Φ` through `d` when
`Φ(f) = J(d f)` for every test object. -/
def IsDifferentialCurrent
    (d : Test →ₗ[𝕜] OneForm) (Φ : Test →ₗ[𝕜] Obs) (J : OneForm →ₗ[𝕜] Obs) : Prop :=
  ∀ f, Φ f = J (d f)

namespace IsDifferentialCurrent

/-- Factorization through `d` is equivalent to equality with the composite `J ∘ d`. -/
theorem iff_eq_comp
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs} {J : OneForm →ₗ[𝕜] Obs} :
    IsDifferentialCurrent d Φ J ↔ Φ = J.comp d := by
  constructor
  · intro h
    exact LinearMap.ext h
  · intro h f
    rw [h]
    rfl

/-- A factorized transport functional vanishes on test objects annihilated by `d`. -/
theorem eq_zero_of_map_eq_zero
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs} {J : OneForm →ₗ[𝕜] Obs}
    (h : IsDifferentialCurrent d Φ J) {f : Test} (hf : d f = 0) :
    Φ f = 0 := by
  rw [h f, hf, map_zero]

/-- Scalar multiplication preserves a differential factorization. -/
theorem smul
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs} {J : OneForm →ₗ[𝕜] Obs}
    (h : IsDifferentialCurrent d Φ J) (c : 𝕜) :
    IsDifferentialCurrent d (c • Φ) (c • J) := by
  intro f
  simp [h f]

/-- Postcomposition by a linear observable map preserves a differential factorization. -/
theorem postcomp
    {Obs' : Type*} [AddCommMonoid Obs'] [Module 𝕜 Obs']
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs} {J : OneForm →ₗ[𝕜] Obs}
    (h : IsDifferentialCurrent d Φ J) (L : Obs →ₗ[𝕜] Obs') :
    IsDifferentialCurrent d (L.comp Φ) (L.comp J) := by
  intro f
  simp only [LinearMap.comp_apply]
  rw [h f]

/-- Choosing a differential current implies the representation-independent statement that transport
depends only on differential data. -/
theorem dependsOnlyOnDifferential
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs} {J : OneForm →ₗ[𝕜] Obs}
    (h : IsDifferentialCurrent d Φ J) :
    DependsOnlyOnDifferential d Φ := by
  intro f g hfg
  rw [h f, h g, hfg]

end IsDifferentialCurrent

/-- Data of one chosen flux functional representing `Φ` through `d`.

No locality or uniqueness claim is bundled into this structure. -/
structure DifferentialCurrentRepresentation
    (d : Test →ₗ[𝕜] OneForm) (Φ : Test →ₗ[𝕜] Obs) where
  /-- The chosen flux functional on differential-like test data. -/
  current : OneForm →ₗ[𝕜] Obs
  /-- Proof that `current` represents the transport through the differential. -/
  isCurrent : IsDifferentialCurrent d Φ current

/-- A bilinear pairing of a current density with 1-form-like test data.

Concrete models are responsible for showing that this supplied pairing has the intended local or
zeroth-order meaning. -/
abbrev LocalCurrentPairing :=
  CurrentDensity →ₗ[𝕜] (OneForm →ₗ[𝕜] Obs)

/-- A transport functional has a local current-density representation relative to a supplied
pairing when one density `j` represents `Φ` through `d`. -/
structure LocalCurrentDensityRepresentation
    (d : Test →ₗ[𝕜] OneForm)
    (Φ : Test →ₗ[𝕜] Obs)
    (pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)) where
  /-- The chosen local current density. -/
  currentDensity : CurrentDensity
  /-- Proof that `currentDensity` represents the transport through the supplied pairing. -/
  isCurrentDensity : IsDifferentialCurrent d Φ (pairing currentDensity)

namespace LocalCurrentDensityRepresentation

/-- A local current-density representation always gives a differential current representation. -/
def toDifferentialCurrentRepresentation
    {d : Test →ₗ[𝕜] OneForm}
    {Φ : Test →ₗ[𝕜] Obs}
    {pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    (R : LocalCurrentDensityRepresentation d Φ pairing) :
    DifferentialCurrentRepresentation d Φ where
  current := pairing R.currentDensity
  isCurrent := R.isCurrentDensity

end LocalCurrentDensityRepresentation

end ConservationLaw
