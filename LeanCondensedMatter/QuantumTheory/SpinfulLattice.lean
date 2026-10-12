import LeanCondensedMatter.Analysis.DiscreteLattice
import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import LeanCondensedMatter.QuantumTheory.SpinHalf
import Mathlib.Data.Prod.Lex

set_option linter.style.header false

/-!
# Finite two-component lattice one-particle operators

A two-component lattice has lexicographically paired spatial and internal indices.
The lexicographic ordering provides a canonical site order for downstream finite
Fock realizations, but these algebraic one-particle matrix operators and their spin-1/2
specialization do not depend on particle statistics.

The internal two-level matrix representation is distinguished from its physical
spin-space interpretation: the former uses `InternalSpace.PauliMatrix`, while the latter
is selected by `QuantumTheory.SpinHalf.spinMatrix`.
-/

namespace QuantumTheory
namespace SpinfulLattice

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
    (SpinfulSite Site →₀ ℂ) →ₗ[ℂ] (SpinfulSite Site →₀ ℂ) := by
  classical
  exact ∑ x : Site, ∑ a : Fin 2, ∑ b : Fin 2,
    S a b • matrixUnit (spinfulSite x a) (spinfulSite x b)

/-- Applying an internal matrix identically at every site is complex-linear in that matrix. -/
noncomputable def internalOneBodyLinear
    {Site : Type*} [Fintype Site] :
    InternalSpace.PauliMatrix →ₗ[ℂ]
      ((SpinfulSite Site →₀ ℂ) →ₗ[ℂ] (SpinfulSite Site →₀ ℂ)) where
  toFun := internalOneBody
  map_add' := by
    classical
    intro S T
    simp [internalOneBody, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    classical
    intro c S
    simp_rw [internalOneBody, Matrix.smul_apply, RingHom.id_apply,
      Finset.smul_sum, smul_smul, smul_eq_mul]

@[simp]
theorem internalOneBodyLinear_apply
    {Site : Type*} [Fintype Site] (S : InternalSpace.PauliMatrix) :
    internalOneBodyLinear (Site := Site) S = internalOneBody S :=
  rfl

variable {Site : Type*} [Fintype Site]

/-- One-particle spin-1/2 observable as a real-linear function of spin space. -/
noncomputable def spinOneBodyLinear
    (spinScale : ℝ) :
    QuantumTheory.SpinHalf.SpinSpace →ₗ[ℝ]
      ((SpinfulSite Site →₀ ℂ) →ₗ[ℂ] (SpinfulSite Site →₀ ℂ)) :=
  ((internalOneBodyLinear (Site := Site)).restrictScalars ℝ).comp
    (QuantumTheory.SpinHalf.spinMatrix spinScale)

/-- One-particle spin-1/2 observable associated with a spin-space component vector. -/
noncomputable def spinOneBody
    (spinScale : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    (SpinfulSite Site →₀ ℂ) →ₗ[ℂ] (SpinfulSite Site →₀ ℂ) :=
  spinOneBodyLinear spinScale spinComponent

@[simp]
theorem spinOneBodyLinear_apply
    (spinScale : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    spinOneBodyLinear (Site := Site) spinScale spinComponent =
      spinOneBody (Site := Site) spinScale spinComponent :=
  rfl

end
end SpinfulLattice
end QuantumTheory
