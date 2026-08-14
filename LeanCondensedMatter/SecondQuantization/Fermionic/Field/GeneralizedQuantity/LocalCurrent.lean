import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeneralizedQuantity.CurrentRepresentation

set_option linter.style.header false

/-!
# Local current-density representations of generalized transport

This module adds the stronger current notion requested by issue #1159.

`CurrentRepresentation.lean` only asks whether a transport functional factors through a
differential-like map,

```text
Φ(f) = J(d f).
```

That does not by itself make `J` a local vector-current density: `J` may differentiate or otherwise
use nonlocal information from its 1-form argument.

Here locality is represented one layer later. A concrete model supplies a bilinear pairing

```text
pairing : CurrentDensity →ₗ[ℂ] (OneForm →ₗ[ℂ] Obs)
```

whose intended downstream realization is a zeroth-order pairing such as

```text
pairing j α = ∫ α(r) · j(r) d r.
```

A `LocalCurrentDensityRepresentation` then chooses a density `j` and proves

```text
Φ(f) = pairing j (d f).
```

The abstract layer deliberately does not try to prove that an arbitrary supplied `pairing` is
pointwise/local. That analytic fact belongs to the concrete continuum, lattice, or distributional
realization defining the pairing. This keeps `SecondQuantization.Fermionic.Field` independent of
the single-particle continuum stack while making the distinction between differential
factorization and local-current representation explicit in the type hierarchy.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

variable {Test OneForm Obs CurrentDensity : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable [AddCommGroup Obs] [Module ℂ Obs]
variable [AddCommGroup CurrentDensity] [Module ℂ CurrentDensity]

/-- A bilinear pairing of a current density with 1-form-like test data.

Concrete models should instantiate this with the intended zeroth-order/local pairing. For example,
in a continuum model this can encode `j, α ↦ ∫ α · j`. -/
abbrev LocalCurrentPairing :=
  CurrentDensity →ₗ[ℂ] (OneForm →ₗ[ℂ] Obs)

/-- Two current densities are weakly equivalent when they give the same pairing against every
exact test 1-form `d f`.

This is the natural equivalence visible to the transport functional. It intentionally allows the
usual kernel/boundary/improvement ambiguity unless a concrete model proves that its test family and
pairing separate current densities. -/
def CurrentDensityEquivalent
    (d : Test →ₗ[ℂ] OneForm)
    (pairing : LocalCurrentPairing (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity))
    (j₁ j₂ : CurrentDensity) : Prop :=
  ∀ f, pairing j₁ (d f) = pairing j₂ (d f)

namespace CurrentDensityEquivalent

/-- Weak current-density equivalence is reflexive. -/
theorem refl
    (d : Test →ₗ[ℂ] OneForm)
    (pairing : LocalCurrentPairing (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity))
    (j : CurrentDensity) :
    CurrentDensityEquivalent d pairing j j := by
  intro f
  rfl

/-- Weak current-density equivalence is symmetric. -/
theorem symm
    {d : Test →ₗ[ℂ] OneForm}
    {pairing : LocalCurrentPairing (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    {j₁ j₂ : CurrentDensity}
    (h : CurrentDensityEquivalent d pairing j₁ j₂) :
    CurrentDensityEquivalent d pairing j₂ j₁ := by
  intro f
  exact (h f).symm

/-- Weak current-density equivalence is transitive. -/
theorem trans
    {d : Test →ₗ[ℂ] OneForm}
    {pairing : LocalCurrentPairing (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    {j₁ j₂ j₃ : CurrentDensity}
    (h₁₂ : CurrentDensityEquivalent d pairing j₁ j₂)
    (h₂₃ : CurrentDensityEquivalent d pairing j₂ j₃) :
    CurrentDensityEquivalent d pairing j₁ j₃ := by
  intro f
  exact (h₁₂ f).trans (h₂₃ f)

end CurrentDensityEquivalent

/-- A transport functional has a local current-density representation relative to a supplied
zeroth-order pairing when one current density `j` represents `Φ` through `d`.

The supplied `pairing` is part of the representation boundary: a concrete model is responsible for
showing that it really is the desired local/zeroth-order pairing rather than a higher-derivative or
nonlocal functional. -/
structure LocalCurrentDensityRepresentation
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ] Obs)
    (pairing : LocalCurrentPairing (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)) where
  /-- The chosen local current density. -/
  currentDensity : CurrentDensity
  /-- The canonical transport functional is the pairing of `currentDensity` with `d f`. -/
  represents : FactorsThroughDifferential d Φ (pairing currentDensity)

namespace LocalCurrentDensityRepresentation

/-- A local current-density representation always gives a differential current representation. -/
def toDifferentialCurrentRepresentation
    {d : Test →ₗ[ℂ] OneForm}
    {Φ : Test →ₗ[ℂ] Obs}
    {pairing : LocalCurrentPairing (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    (R : LocalCurrentDensityRepresentation d Φ pairing) :
    DifferentialCurrentRepresentation d Φ where
  current := pairing R.currentDensity
  factors := R.represents

/-- Evaluate the local current-density representation on one test object. -/
theorem apply
    {d : Test →ₗ[ℂ] OneForm}
    {Φ : Test →ₗ[ℂ] Obs}
    {pairing : LocalCurrentPairing (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    (R : LocalCurrentDensityRepresentation d Φ pairing) (f : Test) :
    Φ f = pairing R.currentDensity (d f) :=
  R.represents f

/-- Any two densities representing the same transport functional are weakly equivalent on exact
test 1-forms. This is the abstract form of current improvement/boundary ambiguity. -/
theorem currentDensityEquivalent
    {d : Test →ₗ[ℂ] OneForm}
    {Φ : Test →ₗ[ℂ] Obs}
    {pairing : LocalCurrentPairing (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    (R₁ R₂ : LocalCurrentDensityRepresentation d Φ pairing) :
    CurrentDensityEquivalent d pairing R₁.currentDensity R₂.currentDensity := by
  intro f
  calc
    pairing R₁.currentDensity (d f) = Φ f := (R₁.represents f).symm
    _ = pairing R₂.currentDensity (d f) := R₂.represents f

end LocalCurrentDensityRepresentation

/-- Exact differential tests and the chosen pairing separate current densities when weak
equivalence already implies equality.

This is deliberately an extra hypothesis rather than part of `LocalCurrentDensityRepresentation`:
without it, current densities are only determined up to the kernel invisible to exact test forms. -/
def SeparatesCurrentDensities
    (d : Test →ₗ[ℂ] OneForm)
    (pairing : LocalCurrentPairing (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)) : Prop :=
  ∀ ⦃j₁ j₂ : CurrentDensity⦄, CurrentDensityEquivalent d pairing j₁ j₂ → j₁ = j₂

/-- A local current density is unique when the concrete differential tests and pairing separate
current densities. -/
theorem localCurrentDensity_unique_of_separates
    {d : Test →ₗ[ℂ] OneForm}
    {Φ : Test →ₗ[ℂ] Obs}
    {pairing : LocalCurrentPairing (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    (hsep : SeparatesCurrentDensities d pairing)
    (R₁ R₂ : LocalCurrentDensityRepresentation d Φ pairing) :
    R₁.currentDensity = R₂.currentDensity :=
  hsep (R₁.currentDensityEquivalent R₂)

end Field
end Fermionic
end SecondQuantization
