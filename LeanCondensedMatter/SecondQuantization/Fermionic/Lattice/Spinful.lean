import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice
import Mathlib.Data.Prod.Lex

set_option linter.style.header false

/-!
# Finite two-level lattice one-particle operators

A two-level lattice is represented by the lexicographically ordered product site type
`Site ×ₗ Fin 2`. The order is bookkeeping for the canonical finite-fermion occupation basis; the
underlying labels remain a spatial site and a two-state internal index.

This module is intentionally neutral about the physical interpretation of that internal space. It
provides the one-particle action of an arbitrary `2 × 2` internal matrix. Spin-1/2 interpretation,
physical polarization directions, current construction, and Kubo response belong downstream.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

open scoped BigOperators

noncomputable section

/-- Lexicographically ordered product of one spatial lattice label and a two-state internal spin. -/
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
