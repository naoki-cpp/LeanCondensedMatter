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

The pairing is deliberately abstract. Concrete continuum models may realize it by a zeroth-order
pairing such as `∫ α · j`, while lattice models may use a finite bond pairing. No locality claim is
made merely from factorization through `d`.

This module does not define current observables in general. Operator-level generalized currents,
model-specific charge-current vertices, and response observables may exist without a weak
differential representation. The composition equality records the additional local-balance fact
that a supplied one-form functional represents `Φ` through `d`; it is not the root definition of
every current operator.

Two currents agree on exact differential data precisely when their compositions with `d` are equal.
Invisible extensions satisfy `K.comp d = 0`. A density is uniquely determined when the map
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
structure DifferentialCurrentRepresentation
    (d : Test →ₗ[𝕜] OneForm) (Φ : Test →ₗ[𝕜] Obs) where
  /-- The chosen flux functional on differential-like test data. -/
  current : OneForm →ₗ[𝕜] Obs
  /-- Proof that `current` represents the transport through the differential. -/
  isCurrent : Φ = current.comp d

namespace DifferentialCurrentRepresentation

/-- Two representations of the same transport differ by an extension vanishing on exact
differential data. -/
theorem exists_current_eq_add_invisible
    {R Test' OneForm' Obs' : Type*} [CommRing R]
    [AddCommMonoid Test'] [Module R Test']
    [AddCommMonoid OneForm'] [Module R OneForm']
    [AddCommGroup Obs'] [Module R Obs']
    {d : Test' →ₗ[R] OneForm'} {Φ : Test' →ₗ[R] Obs'}
    (R₁ R₂ : DifferentialCurrentRepresentation d Φ) :
    ∃ K : OneForm' →ₗ[R] Obs', K.comp d = 0 ∧ R₁.current = R₂.current + K := by
  refine ⟨R₁.current - R₂.current, ?_, ?_⟩
  · apply LinearMap.ext
    intro f
    change R₁.current (d f) - R₂.current (d f) = 0
    have h := R₁.isCurrent.symm.trans R₂.isCurrent
    have hf := congrArg (fun L : Test' →ₗ[R] Obs' => L f) h
    simp only [LinearMap.comp_apply] at hf
    rw [hf, sub_self]
  · apply LinearMap.ext
    intro α
    change R₁.current α = R₂.current α + (R₁.current α - R₂.current α)
    rw [add_comm, sub_add_cancel]

end DifferentialCurrentRepresentation

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

/-- A local current density is unique if the paired exact-differential tests separate densities. -/
theorem localCurrentDensity_unique_of_separates
    {d : Test →ₗ[𝕜] OneForm}
    {Φ : Test →ₗ[𝕜] Obs}
    {pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    (hsep : Function.Injective (fun j : CurrentDensity => (pairing j).comp d))
    (R₁ R₂ : LocalCurrentDensityRepresentation d Φ pairing) :
    R₁.currentDensity = R₂.currentDensity :=
  hsep (R₁.isCurrentDensity.symm.trans R₂.isCurrentDensity)

end ConservationLaw
