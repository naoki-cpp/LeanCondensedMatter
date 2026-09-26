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

/-- Spatial multiplication operator on a spinful lattice.

The scalar weight depends only on the spatial site and acts identically on both internal spin
labels. This is the finite-lattice analogue of a position-space multiplication localizer. -/
noncomputable def spatialMultiplicationOneBody
    {Site : Type*} [Fintype Site] (weight : Site → ℂ) :
    LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site) := by
  classical
  exact ∑ x : Site, ∑ s : Fin 2,
    weight x • matrixUnit (spinfulSite x s) (spinfulSite x s)

@[simp]
theorem spatialMultiplicationOneBody_latticeKet
    {Site : Type*} [Fintype Site]
    (weight : Site → ℂ) (x : Site) (s : Fin 2) :
    spatialMultiplicationOneBody weight (latticeKet (spinfulSite x s)) =
      weight x • latticeKet (spinfulSite x s) := by
  classical
  simp [spatialMultiplicationOneBody, latticeKet, LinearMap.sum_apply, matrixUnit_apply,
    spinfulSite]

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

/-- Spatial multiplication commutes with every uniformly applied internal spin polarization. -/
theorem spatialMultiplicationOneBody_comp_spinPolarizationOneBody_comm
    {Site : Type*} [Fintype Site]
    (weight : Site → ℂ) (spinScale : ℝ)
    (polarization : InternalSpace.PauliAxis → ℝ) :
    (spatialMultiplicationOneBody weight).comp
        (spinPolarizationOneBody spinScale polarization) =
      (spinPolarizationOneBody spinScale polarization).comp
        (spatialMultiplicationOneBody weight) := by
  classical
  apply Common.linearMap_ext_basisState
  rw [Lex.forall, Prod.forall]
  intro x s
  simp [LinearMap.comp_apply, spinPolarizationOneBody, LinearMap.sum_apply,
    spatialMultiplicationOneBody_latticeKet, Common.basisState, latticeKet, matrixUnit_apply,
    spinfulSite, smul_smul]
  module

/-- A spatial multiplication localizer commutes with arbitrary spin polarization. -/
theorem linearCommutator_spatialMultiplicationOneBody_spinPolarizationOneBody
    {Site : Type*} [Fintype Site]
    (weight : Site → ℂ) (spinScale : ℝ)
    (polarization : InternalSpace.PauliAxis → ℝ) :
    _root_.ConservationLaw.linearCommutator
      (spatialMultiplicationOneBody weight)
      (spinPolarizationOneBody spinScale polarization) = 0 := by
  exact sub_eq_zero.mpr
    (spatialMultiplicationOneBody_comp_spinPolarizationOneBody_comm
      weight spinScale polarization)

end
end Lattice
end Fermionic
end SecondQuantization
