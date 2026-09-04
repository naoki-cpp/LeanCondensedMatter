import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak current representations

This module contains representation-independent infrastructure for weak transport functionals.
It is intentionally independent of quantum mechanics and second quantization.

For a linear differential-like map

```text
d : Test →ₗ[𝕜] OneForm
```

and a transport functional

```text
Φ : Test →ₗ[𝕜] Obs,
```

`FactorsThroughDifferential d Φ J` states that `Φ(f) = J(d f)`.  A strictly stronger
`LocalCurrentDensityRepresentation` chooses a current density `j` and a supplied bilinear pairing
such that

```text
Φ(f) = pairing j (d f).
```

The pairing is deliberately abstract.  Concrete continuum models may realize it by a zeroth-order
pairing such as `∫ α · j`, while lattice models may use a finite bond pairing.  No locality claim is
made merely from factorization through `d`.
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs CurrentDensity : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]
variable [AddCommMonoid CurrentDensity] [Module 𝕜 CurrentDensity]

/-- A transport functional `Φ` factors through a differential-like map `d` via `J` when
`Φ(f) = J(d f)` for every test object. -/
def FactorsThroughDifferential
    (d : Test →ₗ[𝕜] OneForm) (Φ : Test →ₗ[𝕜] Obs) (J : OneForm →ₗ[𝕜] Obs) : Prop :=
  ∀ f, Φ f = J (d f)

namespace FactorsThroughDifferential

/-- Factorization through `d` is equivalent to equality with the composite `J ∘ d`. -/
theorem iff_eq_comp
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs} {J : OneForm →ₗ[𝕜] Obs} :
    FactorsThroughDifferential d Φ J ↔ Φ = J.comp d := by
  constructor
  · intro h
    exact LinearMap.ext h
  · intro h f
    rw [h]
    rfl

/-- A factorized transport functional vanishes on test objects annihilated by `d`. -/
theorem eq_zero_of_map_eq_zero
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs} {J : OneForm →ₗ[𝕜] Obs}
    (h : FactorsThroughDifferential d Φ J) {f : Test} (hf : d f = 0) :
    Φ f = 0 := by
  rw [h f, hf, map_zero]

/-- Scalar multiplication preserves a differential factorization. -/
theorem smul
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs} {J : OneForm →ₗ[𝕜] Obs}
    (h : FactorsThroughDifferential d Φ J) (c : 𝕜) :
    FactorsThroughDifferential d (c • Φ) (c • J) := by
  intro f
  simp [h f]

/-- Postcomposition by a linear observable map preserves a differential factorization. -/
theorem postcomp
    {Obs' : Type*} [AddCommMonoid Obs'] [Module 𝕜 Obs']
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs} {J : OneForm →ₗ[𝕜] Obs}
    (h : FactorsThroughDifferential d Φ J) (L : Obs →ₗ[𝕜] Obs') :
    FactorsThroughDifferential d (L.comp Φ) (L.comp J) := by
  intro f
  simp only [LinearMap.comp_apply]
  rw [h f]

end FactorsThroughDifferential

/-- Data of one chosen flux functional representing `Φ` through `d`.

No locality or uniqueness claim is bundled into this structure. -/
structure DifferentialCurrentRepresentation
    (d : Test →ₗ[𝕜] OneForm) (Φ : Test →ₗ[𝕜] Obs) where
  /-- The chosen flux functional on differential-like test data. -/
  current : OneForm →ₗ[𝕜] Obs
  /-- Proof that the transport functional is represented by `current ∘ d`. -/
  factors : FactorsThroughDifferential d Φ current

/-- A bilinear pairing of a current density with 1-form-like test data.

Concrete models are responsible for showing that this supplied pairing has the intended local or
zeroth-order meaning. -/
abbrev LocalCurrentPairing :=
  CurrentDensity →ₗ[𝕜] (OneForm →ₗ[𝕜] Obs)

/-- Two current densities are weakly equivalent when they pair equally against every exact test
1-form `d f`. -/
def CurrentDensityEquivalent
    (d : Test →ₗ[𝕜] OneForm)
    (pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity))
    (j₁ j₂ : CurrentDensity) : Prop :=
  ∀ f, pairing j₁ (d f) = pairing j₂ (d f)

namespace CurrentDensityEquivalent

/-- Weak current-density equivalence is reflexive. -/
theorem refl
    (d : Test →ₗ[𝕜] OneForm)
    (pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity))
    (j : CurrentDensity) :
    CurrentDensityEquivalent d pairing j j := by
  intro f
  rfl

/-- Weak current-density equivalence is symmetric. -/
theorem symm
    {d : Test →ₗ[𝕜] OneForm}
    {pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    {j₁ j₂ : CurrentDensity}
    (h : CurrentDensityEquivalent d pairing j₁ j₂) :
    CurrentDensityEquivalent d pairing j₂ j₁ := by
  intro f
  exact (h f).symm

/-- Weak current-density equivalence is transitive. -/
theorem trans
    {d : Test →ₗ[𝕜] OneForm}
    {pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    {j₁ j₂ j₃ : CurrentDensity}
    (h₁₂ : CurrentDensityEquivalent d pairing j₁ j₂)
    (h₂₃ : CurrentDensityEquivalent d pairing j₂ j₃) :
    CurrentDensityEquivalent d pairing j₁ j₃ := by
  intro f
  exact (h₁₂ f).trans (h₂₃ f)

end CurrentDensityEquivalent

/-- A transport functional has a local current-density representation relative to a supplied
pairing when one density `j` represents `Φ` through `d`. -/
structure LocalCurrentDensityRepresentation
    (d : Test →ₗ[𝕜] OneForm)
    (Φ : Test →ₗ[𝕜] Obs)
    (pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)) where
  /-- The chosen local current density. -/
  currentDensity : CurrentDensity
  /-- The transport functional is the pairing of `currentDensity` with `d f`. -/
  represents : FactorsThroughDifferential d Φ (pairing currentDensity)

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
  factors := R.represents

/-- Any two densities representing the same transport functional are weakly equivalent on exact
test 1-forms. -/
theorem currentDensityEquivalent
    {d : Test →ₗ[𝕜] OneForm}
    {Φ : Test →ₗ[𝕜] Obs}
    {pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    (R₁ R₂ : LocalCurrentDensityRepresentation d Φ pairing) :
    CurrentDensityEquivalent d pairing R₁.currentDensity R₂.currentDensity := by
  intro f
  calc
    pairing R₁.currentDensity (d f) = Φ f := (R₁.represents f).symm
    _ = pairing R₂.currentDensity (d f) := R₂.represents f

end LocalCurrentDensityRepresentation

/-- Exact differential tests and the chosen pairing separate current densities when weak
equivalence implies equality. -/
def SeparatesCurrentDensities
    (d : Test →ₗ[𝕜] OneForm)
    (pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)) : Prop :=
  ∀ ⦃j₁ j₂ : CurrentDensity⦄, CurrentDensityEquivalent d pairing j₁ j₂ → j₁ = j₂

/-- A local current density is unique when the concrete differential tests and pairing separate
current densities. -/
theorem localCurrentDensity_unique_of_separates
    {d : Test →ₗ[𝕜] OneForm}
    {Φ : Test →ₗ[𝕜] Obs}
    {pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    (hsep : SeparatesCurrentDensities d pairing)
    (R₁ R₂ : LocalCurrentDensityRepresentation d Φ pairing) :
    R₁.currentDensity = R₂.currentDensity :=
  hsep (R₁.currentDensityEquivalent R₂)

end ConservationLaw
