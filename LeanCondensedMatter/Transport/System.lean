import LeanCondensedMatter.QuantumTheory.Postulates
import LeanCondensedMatter.Transport.FiniteVolume

set_option linter.style.header false

/-!
# Bounded transport-system conventions

This module fixes the common data and sign conventions for the clean,
zero-temperature Kubo–Bastin/Kubo–Středa development tracked by issue #365.

The base structure is intentionally dimension-independent: the Hamiltonian and current
components are bounded self-adjoint operators on an arbitrary complete complex Hilbert
space. Finite-dimensionality, trace-class assumptions, and trace-per-unit-volume
hypotheses belong on the theorems that need them rather than in the reusable system data.

The Fermi projector is supplied as an independent orthogonal projector commuting with
the Hamiltonian. Constructing the discontinuous spectral projector from a functional
calculus is deliberately left to a later theorem.

Retarded and advanced spectral parameters use

```text
zᴿ(E, η) = E + i η,
zᴬ(E, η) = E - i η,
```

with `η > 0`. Corresponding resolvents can therefore be defined as
`(zᴿ(E, η) I - H)⁻¹` and `(zᴬ(E, η) I - H)⁻¹` once the required inverse API is available.

Physical finite-volume normalization is represented separately by `PositiveVolume` and reused by
`FiniteVolumeSystem`. An infinite-dimensional Hilbert space may still describe a finite-volume
system; this is distinct from an infinite-volume or thermodynamic-limit construction.

This module fixes data only. It does not prove linear response, define a source coupling,
or adopt a Kubo–Bastin trace formula as a foundational conductivity law.
-/

namespace QuantumTheory
namespace Transport

/-- Cartesian labels for current components in the first conductivity tensor. -/
inductive CartesianDirection where
  | x
  | y
  | z
  deriving DecidableEq, Fintype

/-- The retarded spectral parameter `E + iη`. -/
def retardedSpectralParameter (energy broadening : ℝ) : ℂ :=
  (energy : ℂ) + (broadening : ℂ) * Complex.I

/-- The advanced spectral parameter `E - iη`. -/
def advancedSpectralParameter (energy broadening : ℝ) : ℂ :=
  (energy : ℂ) - (broadening : ℂ) * Complex.I

@[simp]
theorem retardedSpectralParameter_re (energy broadening : ℝ) :
    (retardedSpectralParameter energy broadening).re = energy := by
  simp [retardedSpectralParameter]

@[simp]
theorem retardedSpectralParameter_im (energy broadening : ℝ) :
    (retardedSpectralParameter energy broadening).im = broadening := by
  simp [retardedSpectralParameter]

@[simp]
theorem advancedSpectralParameter_re (energy broadening : ℝ) :
    (advancedSpectralParameter energy broadening).re = energy := by
  simp [advancedSpectralParameter]

@[simp]
theorem advancedSpectralParameter_im (energy broadening : ℝ) :
    (advancedSpectralParameter energy broadening).im = -broadening := by
  simp [advancedSpectralParameter]

/--
Bounded clean-system data common to finite- and infinite-dimensional Hilbert spaces.

`current α` is the physical current observable in direction `α`. The signed carrier
charge is recorded separately so later model-specific constructions can state
`J = qv` without multiplying by the charge twice in the response formula.
-/
structure BoundedSystem (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- Bounded self-adjoint Hamiltonian. -/
  hamiltonian : Observable H
  /-- Bounded physical current observables for the three Cartesian directions. -/
  current : CartesianDirection → Observable H
  /-- Signed carrier charge used when a model derives current from velocity. -/
  charge : ℝ
  /-- Reduced Planck constant in the chosen unit system. -/
  reducedPlanckConstant : ℝ
  reducedPlanckConstant_pos : 0 < reducedPlanckConstant
  /-- Zero-temperature Fermi energy. Occupied states satisfy energy `≤ fermiEnergy`. -/
  fermiEnergy : ℝ
  /-- Positive retarded/advanced broadening parameter `η`. -/
  broadening : ℝ
  broadening_pos : 0 < broadening
  /-- The zero-temperature spectral projector `1_{(-∞, μ]}(H)`. -/
  fermiProjector : H →L[ℂ] H
  fermiProjector_selfAdjoint : IsSelfAdjoint fermiProjector
  fermiProjector_idempotent : fermiProjector ∘L fermiProjector = fermiProjector
  fermiProjector_commutes_hamiltonian :
    fermiProjector ∘L hamiltonian.1 = hamiltonian.1 ∘L fermiProjector

/-- A bounded transport system equipped with canonical positive finite-volume data. -/
structure FiniteVolumeSystem (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] extends BoundedSystem H, PositiveVolume

namespace BoundedSystem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Retarded parameter at the system's Fermi energy and chosen broadening. -/
def retardedFermiParameter (system : BoundedSystem H) : ℂ :=
  retardedSpectralParameter system.fermiEnergy system.broadening

/-- Advanced parameter at the system's Fermi energy and chosen broadening. -/
def advancedFermiParameter (system : BoundedSystem H) : ℂ :=
  advancedSpectralParameter system.fermiEnergy system.broadening

/-- Positivity of the stored reduced Planck constant implies nonvanishing. -/
theorem reducedPlanckConstant_ne_zero (system : BoundedSystem H) :
    system.reducedPlanckConstant ≠ 0 :=
  ne_of_gt system.reducedPlanckConstant_pos

/-- Positivity of the stored broadening implies nonvanishing. -/
theorem broadening_ne_zero (system : BoundedSystem H) :
    system.broadening ≠ 0 :=
  ne_of_gt system.broadening_pos

end BoundedSystem

end Transport
end QuantumTheory
