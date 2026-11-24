import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Weak current representations

This module contains representation-specific infrastructure for weak transport functionals.
Dependence on the differential without a chosen current is expressed directly by
Mathlib's `Function.FactorsThrough` in `FluxBalanceLaw`.

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

Both representations are ordinary subtype fibers of the corresponding transport map.
The pairing is deliberately abstract. Concrete continuum models may realize it by a zeroth-order
pairing such as `∫ α · j`, while lattice models may use a finite bond pairing. No locality claim is
made merely from factorization through `d`.

This module does not define current observables in general. Operator-level generalized currents,
model-specific charge-current vertices, and response observables may exist without a weak
differential representation. The composition equality records the additional local-balance fact
that a supplied one-form functional represents `Φ` through `d`; it is not the root definition of
every current operator.

Two currents agree on exact differential data precisely when their compositions with `d` are equal.
Invisible extensions satisfy `K.comp d = 0`; differences of representatives are handled by
`LinearMap.sub_comp`. A density is uniquely determined when the map
`j ↦ (pairing j).comp d` is injective. These use ordinary equality and injectivity, not a separate
current-specific equivalence relation.
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
abbrev DifferentialCurrentRepresentation
    (d : Test →ₗ[𝕜] OneForm) (Φ : Test →ₗ[𝕜] Obs) :=
  {J : OneForm →ₗ[𝕜] Obs // Φ = J.comp d}

/-- A bilinear pairing of a current density with 1-form-like test data.

Concrete models are responsible for showing that this supplied pairing has the intended local or
zeroth-order meaning. -/
abbrev LocalCurrentPairing :=
  CurrentDensity →ₗ[𝕜] (OneForm →ₗ[𝕜] Obs)

/-- A transport functional has a local current-density representation relative to a supplied
pairing when one density `j` represents `Φ` through `d`. -/
abbrev LocalCurrentDensityRepresentation
    (d : Test →ₗ[𝕜] OneForm)
    (Φ : Test →ₗ[𝕜] Obs)
    (pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)) :=
  {j : CurrentDensity // Φ = (pairing j).comp d}

/-- A local current density is unique if the paired exact-differential tests separate densities. -/
theorem localCurrentDensity_unique_of_separates
    {d : Test →ₗ[𝕜] OneForm}
    {Φ : Test →ₗ[𝕜] Obs}
    {pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    (hsep : Function.Injective (fun j : CurrentDensity => (pairing j).comp d))
    (R₁ R₂ : LocalCurrentDensityRepresentation d Φ pairing) :
    R₁.val = R₂.val :=
  hsep (R₁.property.symm.trans R₂.property)

end ConservationLaw
