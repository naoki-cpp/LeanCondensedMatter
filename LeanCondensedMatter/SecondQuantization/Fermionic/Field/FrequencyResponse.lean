import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricCurrent
import LeanCondensedMatter.QuantumTheory.LinearResponse.RetardedSusceptibility

set_option linter.style.header false

/-!
# Finite-time adiabatic frequency response

The geometric current theorem is a bounded finite-volume statement in the time domain. This module
introduces the next, deliberately weaker layer needed by conductivity: a complexified finite-time
frequency coefficient with a strictly positive switching rate.

For a source proportional to

```text
exp (η t) exp (-i ω t),
```

factoring out its value at the observation time leaves the lag factor

```text
exp ((-η + i ω) τ).
```

The definitions below do not assert an infinite-time, zero-switching, or DC limit. Instead, those
limits are represented by separate predicates, and the two physically distinct orders

```text
T → ∞, then η → 0⁺, then ω → 0
T → ∞, then ω → 0, then η → 0⁺
```

are recorded independently. This prevents a finite regularized coefficient from being silently
identified with a DC conductivity.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

open Lattice

noncomputable section

/-- Adiabatically damped oscillatory factor for a positive time lag. -/
def adiabaticFrequencyFactor (ω η τ : ℝ) : ℂ :=
  Complex.exp ((-(η : ℂ) + Complex.I * (ω : ℂ)) * (τ : ℂ))

@[simp]
theorem adiabaticFrequencyFactor_zero_lag (ω η : ℝ) :
    adiabaticFrequencyFactor ω η 0 = 1 := by
  simp [adiabaticFrequencyFactor]

@[simp]
theorem adiabaticFrequencyFactor_zero_switching (ω τ : ℝ) :
    adiabaticFrequencyFactor ω 0 τ =
      Complex.exp (Complex.I * (ω : ℂ) * (τ : ℂ)) := by
  simp [adiabaticFrequencyFactor]

@[simp]
theorem adiabaticFrequencyFactor_zero_frequency (η τ : ℝ) :
    adiabaticFrequencyFactor 0 η τ =
      Complex.exp (-(η : ℂ) * (τ : ℂ)) := by
  simp [adiabaticFrequencyFactor]

/-- Finite-observation-time adiabatic transform of a scalar causal kernel. No limit is taken. -/
noncomputable def finiteTimeAdiabaticTransform
    (kernel : ℝ → ℂ) (ω η T : ℝ) : ℂ :=
  ∫ τ in (0 : ℝ)..T, adiabaticFrequencyFactor ω η τ * kernel τ

@[simp]
theorem finiteTimeAdiabaticTransform_zero_time
    (kernel : ℝ → ℂ) (ω η : ℝ) :
    finiteTimeAdiabaticTransform kernel ω η 0 = 0 := by
  simp [finiteTimeAdiabaticTransform]

/-- Existence of the observation-time limit `T → +∞` at fixed `ω` and `η`. -/
def HasInfiniteObservationTimeLimit
    (response : ℝ → ℂ) (value : ℂ) : Prop :=
  Filter.Tendsto response Filter.atTop (nhds value)

/-- Existence of the one-sided zero-switching limit `η → 0⁺`. -/
def HasZeroSwitchingLimit
    (response : ℝ → ℂ) (value : ℂ) : Prop :=
  Filter.Tendsto response (nhdsWithin 0 (Set.Ioi 0)) (nhds value)

/-- Existence of the frequency limit `ω → 0` at fixed values of the other regulators. -/
def HasDCFrequencyLimit
    (response : ℝ → ℂ) (value : ℂ) : Prop :=
  Filter.Tendsto response (nhds 0) (nhds value)

/-- The order `T → ∞`, then `η → 0⁺`, then `ω → 0`.

The intermediate functions are explicit data rather than hidden choices. -/
def HasTimeThenSwitchingThenDCLimit
    (response : ℝ → ℝ → ℝ → ℂ)
    (afterTime : ℝ → ℝ → ℂ)
    (afterSwitching : ℝ → ℂ)
    (dcValue : ℂ) : Prop :=
  (∀ ω η, HasInfiniteObservationTimeLimit
      (response ω η) (afterTime ω η)) ∧
    (∀ ω, HasZeroSwitchingLimit
      (afterTime ω) (afterSwitching ω)) ∧
    HasDCFrequencyLimit afterSwitching dcValue

/-- The distinct order `T → ∞`, then `ω → 0`, then `η → 0⁺`. -/
def HasTimeThenDCThenSwitchingLimit
    (response : ℝ → ℝ → ℝ → ℂ)
    (afterTime : ℝ → ℝ → ℂ)
    (afterDC : ℝ → ℂ)
    (value : ℂ) : Prop :=
  (∀ ω η, HasInfiniteObservationTimeLimit
      (response ω η) (afterTime ω η)) ∧
    (∀ η, HasDCFrequencyLimit
      (fun ω => afterTime ω η) (afterDC η)) ∧
    HasZeroSwitchingLimit afterDC value

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Retarded part of the finite-time, adiabatically regularized directional-current coefficient.

The observation-time source value has been factored out, leaving the lag factor
`exp ((-η + iω) (T - s))`. This is an exact finite-`T`, finite-`η` definition. -/
noncomputable def finiteTimeAdiabaticDirectionalRetardedCoefficient
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η T : ℝ) : ℂ :=
  let J := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  ∫ s in (0 : ℝ)..T,
    adiabaticFrequencyFactor ω η (T - s) *
      QuantumTheory.LinearResponse.retardedSusceptibility
        system expectation J J T s

/-- Contact part of the directional-current coefficient at the observation time. -/
noncomputable def boundedDirectionalContactExpectation
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q T : ℝ) : ℂ :=
  expectation
    (QuantumTheory.LinearResponse.heisenbergEvolution system
      (boundedDirectionalContact geometry direction
        (system.hbar : ℂ) (q : ℂ) K) T)

/-- Total finite-time adiabatic directional-current coefficient: retarded state response plus the
explicit geometric contact response. This is not yet named a DC conductivity. -/
noncomputable def finiteTimeAdiabaticDirectionalCoefficient
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η T : ℝ) : ℂ :=
  finiteTimeAdiabaticDirectionalRetardedCoefficient
      system expectation geometry direction K q ω η T +
    boundedDirectionalContactExpectation
      system expectation geometry direction K q T

/-- The total regularized coefficient exposes the retarded and contact contributions separately. -/
theorem finiteTimeAdiabaticDirectionalCoefficient_eq
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η T : ℝ) :
    finiteTimeAdiabaticDirectionalCoefficient
        system expectation geometry direction K q ω η T =
      finiteTimeAdiabaticDirectionalRetardedCoefficient
          system expectation geometry direction K q ω η T +
        boundedDirectionalContactExpectation
          system expectation geometry direction K q T := by
  rfl

end
end Field
end Fermionic
end SecondQuantization
