import LeanCondensedMatter.Transport.System
import LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics

set_option linter.style.header false

/-!
# Bridge from transport conventions to bounded linear response

`Transport.BoundedSystem` stores the additional current, Fermi, charge, and broadening data needed
by the transport program. Its Hamiltonian and reduced Planck constant canonically determine the
smaller `LinearResponse.BoundedFreeSystem` consumed by the causal Kubo API.

The bridge is one-way: the general linear-response structure intentionally does not acquire
transport-specific Fermi or current data.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Forget transport-specific data and retain the bounded free dynamics used by linear response. -/
def BoundedSystem.toBoundedFreeSystem
    (system : BoundedSystem H) : LinearResponse.BoundedFreeSystem H where
  hamiltonian := system.hamiltonian
  hbar := system.reducedPlanckConstant
  hbar_pos := system.reducedPlanckConstant_pos

@[simp]
theorem BoundedSystem.toBoundedFreeSystem_hamiltonian
    (system : BoundedSystem H) :
    system.toBoundedFreeSystem.hamiltonian = system.hamiltonian :=
  rfl

@[simp]
theorem BoundedSystem.toBoundedFreeSystem_hbar
    (system : BoundedSystem H) :
    system.toBoundedFreeSystem.hbar = system.reducedPlanckConstant :=
  rfl

end
end Transport
end QuantumTheory
