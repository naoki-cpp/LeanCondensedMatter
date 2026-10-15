import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak current representations

This module contains representation-specific infrastructure for weak transport functionals.
Intrinsic dependence on the differential without a chosen current is expressed directly by
Mathlib's `Function.FactorsThrough` in `IntrinsicBalanceLaw`.

For a linear differential-like map

```text
d : Test →ₗ[𝕜] OneForm
```

and a transport functional

```text
Φ : Test →ₗ[𝕜] Obs,
```

An equality `Φ = J.comp d` records a chosen linear current extension with
`Φ(f) = J(d f)`. A strictly stronger `LocalCurrentDensityRepresentation` chooses a current
density `j` and a supplied bilinear pairing such that `Φ(f) = pairing j (d f)`.

The pairing is deliberately abstract. Concrete continuum models may realize it by a zeroth-order
pairing such as `∫ α · j`, while lattice models may use a finite bond pairing. No locality claim is
made merely from factorization through `d`.

This module does not define current observables in general. Operator-level generalized currents,
model-specific charge-current vertices, and response observables may exist without a weak
differential representation. The composition equality records the additional local-balance fact
that a supplied one-form functional represents `Φ` through `d`; it is not the root definition of
every current operator.
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs CurrentDensity : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]
variable [AddCommMonoid CurrentDensity] [Module 𝕜 CurrentDensity]

/-- Data of one chosen flux functional representing `Φ` through `d`.

No locality or uniqueness claim is bundled into this structure. -/
structure DifferentialCurrentRepresentation
    (d : Test →ₗ[𝕜] OneForm) (Φ : Test →ₗ[𝕜] Obs) where
  /-- The chosen flux functional on differential-like test data. -/
  current : OneForm →ₗ[𝕜] Obs
  /-- Proof that `current` represents the transport through the differential. -/
  isCurrent : Φ = current.comp d

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
  isCurrentDensity : Φ = (pairing currentDensity).comp d

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
