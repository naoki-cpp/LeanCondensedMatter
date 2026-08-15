import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice

set_option linter.style.header false

/-!
# Finite spinful lattice one-particle operators

A spinful lattice is represented by the product site type `Site × Fin 2`. The spatial label and the
internal spin label remain explicit, so later spin-orbit hopping models can act on the same canonical
`LatticeState` representation used by the finite-lattice transport stack.

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

/-- Product site type for one spatial lattice label and a two-state internal spin. -/
abbrev SpinfulSite (Site : Type*) := Site × Fin 2

/-- Eigenvalue of the finite spin-z operator on one internal spin label. -/
def spinZWeight (spinScale : ℂ) (s : Fin 2) : ℂ :=
  if s = 0 then spinScale / 2 else -(spinScale / 2)

/-- Diagonal one-particle spin-z operator on a finite spinful lattice. -/
noncomputable def spinZOneBody
    {Site : Type*} [Fintype Site] (spinScale : ℂ) :
    LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site) := by
  classical
  exact ∑ x : Site, ∑ s : Fin 2,
    spinZWeight spinScale s • matrixUnit (x, s) (x, s)

end
end Lattice
end Fermionic
end SecondQuantization
