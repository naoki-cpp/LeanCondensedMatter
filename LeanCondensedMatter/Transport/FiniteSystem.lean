import LeanCondensedMatter.QuantumTheory.Postulates
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option linter.style.header false

/-!
# Finite-system transport conventions

This module fixes the data and sign conventions for the first finite-dimensional,
zero-temperature Kubo–Bastin/Kubo–Středa development tracked by issue #365.

The Hamiltonian and current components are bounded self-adjoint operators on a
finite-dimensional complex Hilbert space. The Fermi projector is supplied as an
independent orthogonal projector commuting with the Hamiltonian; constructing it
from continuous functional calculus is deliberately left to a later theorem.

Retarded and advanced spectral parameters use

```text
zᴿ(E, η) = E + i η,
zᴬ(E, η) = E - i η,
```

with `η > 0`. The corresponding resolvents will therefore be defined in the next
transport layer as `(zᴿ(E, η) I - H)⁻¹` and `(zᴬ(E, η) I - H)⁻¹`.

The scope is finite volume and finite dimension. No thermodynamic limit, disorder
average, finite-temperature Fermi–Dirac weight, or current-from-position construction
is included here.
-/

namespace QuantumTheory
namespace Transport

/-- Cartesian labels for the current components used in the first conductivity tensor. -/
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

/--
Data for the clean finite-system conductivity problem.

`current α` is the physical current observable in direction `α`. The signed carrier
charge is recorded separately so later model-specific constructions can state
`J = qv` without multiplying by the charge twice in the response formula.
-/
structure FiniteSystem (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] where
  /-- Self-adjoint finite-system Hamiltonian. -/
  hamiltonian : Observable H
  /-- Physical current observables for the three Cartesian directions. -/
  current : CartesianDirection → Observable H
  /-- Finite sample volume. -/
  volume : ℝ
  volume_pos : 0 < volume
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

namespace FiniteSystem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Retarded parameter at the system's Fermi energy and chosen broadening. -/
def retardedFermiParameter (system : FiniteSystem H) : ℂ :=
  retardedSpectralParameter system.fermiEnergy system.broadening

/-- Advanced parameter at the system's Fermi energy and chosen broadening. -/
def advancedFermiParameter (system : FiniteSystem H) : ℂ :=
  advancedSpectralParameter system.fermiEnergy system.broadening

end FiniteSystem

end Transport
end QuantumTheory
