import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricCurrent
import LeanCondensedMatter.QuantumTheory.LinearResponse.RetardedSusceptibility

set_option linter.style.header false

/-!
# Finite-time fermionic directional frequency response

The generic scalar finite-time adiabatic transform and observation-time convergence predicate now
live in `QuantumTheory.LinearResponse.FiniteTimeAdiabatic`; regulator/static limit orderings are
owned by `QuantumTheory.LinearResponse.LimitOrder`.

This module retains the finite-lattice fermionic realization needed by conductivity: a complexified
finite-time coefficient built from the continuity-derived directional current and the explicit
Peierls contact response. For a source proportional to

```text
exp (η t) exp (-i ω t),
```

factoring out its value at the observation time leaves the lag factor

```text
exp ((-η + i ω) τ).
```

No infinite-time, zero-switching, DC, or thermodynamic limit is asserted here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

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
end Transport
end Fermionic
end SecondQuantization
