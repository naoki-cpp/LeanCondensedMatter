import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice
import Mathlib.Data.Prod.Lex

set_option linter.style.header false

/-!
# Finite spinful lattice one-particle operators

A spinful lattice is represented by the lexicographically ordered product site type
`Site ×ₗ Fin 2`. The order is bookkeeping for the canonical finite-fermion occupation basis; the
underlying labels remain a spatial site and an explicit two-state internal spin. Later spin-orbit
hopping models can therefore act on the same canonical `LatticeState` representation used by the
finite-lattice transport stack.

For a real polarization family `p` over the three Pauli axes, this module exposes the one-particle
spin operator

```text
S_p = (s/2) (p_x σ_x + p_y σ_y + p_z σ_z).
```

No normalization condition is imposed on `p`; a downstream physical model may require a unit
polarization vector when appropriate. The spin scale `s : ℝ` is physically `ℏ`. Current
construction and Kubo response remain downstream in `Fermionic.Transport`.
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

/-- One-particle spin operator for an arbitrary real polarization in the Pauli basis.

The same internal `2 × 2` matrix acts at every spatial site. Real polarization coefficients and
real `spinScale` make the underlying spin matrix Hermitian; normalization of the polarization is
left to downstream model assumptions. -/
noncomputable def spinPolarizationOneBody
    {Site : Type*} [Fintype Site]
    (spinScale : ℝ) (polarization : InternalSpace.PauliAxis → ℝ) :
    LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site) := by
  classical
  let spinMatrix : InternalSpace.PauliMatrix :=
    (((spinScale / 2 : ℝ) : ℂ)) •
      InternalSpace.pauliCombination (fun axis => (polarization axis : ℂ))
  exact ∑ x : Site, ∑ a : Fin 2, ∑ b : Fin 2,
    spinMatrix a b • matrixUnit (spinfulSite x a) (spinfulSite x b)

end
end Lattice
end Fermionic
end SecondQuantization
