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

This module starts with the diagonal spin-z operator

```text
S_z |x,↑⟩ = +(s/2) |x,↑⟩,
S_z |x,↓⟩ = -(s/2) |x,↓⟩,
```

where `s : ℂ` is the spin scale (physically `ℏ`). It is deliberately a one-particle model operator;
current construction and Kubo response remain downstream in `Fermionic.Transport`.
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

/-- Eigenvalue of the finite spin-z operator on one internal spin label. -/
def spinZWeight (spinScale : ℂ) (s : Fin 2) : ℂ :=
  if s = 0 then spinScale / 2 else -(spinScale / 2)

/-- Diagonal one-particle spin-z operator on a finite spinful lattice. -/
noncomputable def spinZOneBody
    {Site : Type*} [Fintype Site] (spinScale : ℂ) :
    LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site) := by
  classical
  exact ∑ x : Site, ∑ s : Fin 2,
    spinZWeight spinScale s • matrixUnit (spinfulSite x s) (spinfulSite x s)

end
end Lattice
end Fermionic
end SecondQuantization
