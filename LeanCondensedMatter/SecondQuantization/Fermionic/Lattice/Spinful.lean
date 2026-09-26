import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice
import Mathlib.Data.Prod.Lex

set_option linter.style.header false

/-!
# Finite spinful lattice one-particle operators

A spinful lattice is represented by the lexicographically ordered product site type
`Site ×ₗ Fin 2`. The order is bookkeeping for the canonical finite-fermion occupation basis; the
`Fin 2` label is the two-component representation space, not a physical polarization direction.

This module provides the one-particle action of an arbitrary `2 × 2` matrix on that internal
representation. The map from a physical-space polarization vector to the corresponding spin-1/2
matrix, current construction, and Kubo response belong downstream.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

open scoped BigOperators

noncomputable section

/-- Lexicographically ordered product of one spatial lattice label and a two-component internal spin representation. -/
abbrev SpinfulSite (Site : Type*) := Site ×ₗ Fin 2

/-- Canonical spinful site with spatial label `x` and internal label `s`. -/
def spinfulSite {Site : Type*} (x : Site) (s : Fin 2) : SpinfulSite Site :=
  toLex (x, s)

/-- Apply one internal `2 × 2` matrix identically at every spatial lattice site. -/
noncomputable def internalOneBody
    {Site : Type*} [Fintype Site] (S : InternalSpace.PauliMatrix) :
    LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site) := by
  classical
  exact ∑ x : Site, ∑ a : Fin 2, ∑ b : Fin 2,
    S a b • matrixUnit (spinfulSite x a) (spinfulSite x b)

end
end Lattice
end Fermionic
end SecondQuantization
