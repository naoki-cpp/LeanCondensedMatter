import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricCurrent
import LeanCondensedMatter.QuantumTheory.LinearResponse.FiniteTimeAdiabatic

set_option linter.style.header false

/-!
# Finite-time fermionic directional frequency response

This module specializes the generic finite-time adiabatic transform to the directional current
response of a finite fermionic lattice. The response combines the continuity-derived directional
current with the explicit Peierls contact contribution.

For a source proportional to

```text
exp (η t) exp (-i ω t),
```

factoring out its value at the observation time leaves the canonical linear-response lag phase

```text
exp ((-η + i ω) τ).
```

No infinite-observation-time, zero-switching, DC, or thermodynamic limit is asserted here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse

noncomputable section

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Neutral response channel for the finite-lattice directional charge current.

The measured and source operators are the same directional current, while the explicit first-order
observable variation is the Peierls contact operator. -/
noncomputable def boundedDirectionalResponseChannel
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q : ℝ) :
    QuantumTheory.LinearResponse.ResponseChannel (FiniteLatticeHilbertFock Site) where
  measured := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  source := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  observableVariation := boundedDirectionalContact geometry direction
    (system.hbar : ℂ) (q : ℂ) K

/-- Retarded part of the finite-time, adiabatically regularized directional-current coefficient.

The observation-time source value has been factored out, leaving the canonical lag phase
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
    adiabaticFrequencyPhase ω η (T - s) *
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

/-- Total finite-time adiabatic directional-current coefficient carried by the neutral response
channel. This is not yet named a DC conductivity. -/
noncomputable def finiteTimeAdiabaticDirectionalCoefficient
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η T : ℝ) : ℂ :=
  (boundedDirectionalResponseChannel system geometry direction K q).finiteTimeAdiabaticResponse
    system expectation ω η T

/-- Expanding the channel-level finite-time response recovers the historical retarded-plus-contact
directional-current coefficient exactly. -/
theorem finiteTimeAdiabaticDirectionalCoefficient_eq_retarded_add_contact
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
