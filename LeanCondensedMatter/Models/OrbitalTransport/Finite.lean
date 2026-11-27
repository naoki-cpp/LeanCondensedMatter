import LeanCondensedMatter.Combinatorics.FiniteAntisymmetricSum
import LeanCondensedMatter.Analysis.Matrix.Pauli
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Finite two-orbital crystal-field torque

The orbitals are the two-dimensional internal `p_x/p_y` subspace.  In units
`ℏ = 1`, the dimensionless local orbital polarization is `L_z = σ_y`, and
a crystal-field splitting `H_cf = Δ σ_z` generates

`i[H_cf,L_z] = 2Δ σ_x`.

A finite, closed collection of such sites with a nonzero *total* orbital
torque cannot absorb that torque into antisymmetric intersite bond currents.
This is a counterexample to universal torque-free orbital continuity, not a
claim about the physical orbital-current density in a real material.
-/

namespace QuantumTheory.Models.OrbitalTransport

open scoped BigOperators

/-- Onsite crystal-field splitting between two real orbitals. -/
noncomputable def crystalFieldHamiltonian (Δ : ℝ) : InternalSpace.PauliMatrix :=
  (Δ : ℂ) • InternalSpace.pauliZ

/-- The two-orbital angular momentum `L_z` in units `ℏ = 1`. -/
def orbitalZ : InternalSpace.PauliMatrix :=
  InternalSpace.pauliY

/-- The local Heisenberg torque `i[H_cf,L_z]` in units `ℏ = 1`. -/
noncomputable def crystalFieldOrbitalTorque (Δ : ℝ) : InternalSpace.PauliMatrix :=
  Complex.I •
    (crystalFieldHamiltonian Δ * orbitalZ - orbitalZ * crystalFieldHamiltonian Δ)

/-- Explicit nonconservation of local orbital angular momentum by the
crystal field, even in the absence of spin-orbit coupling. -/
theorem crystalFieldOrbitalTorque_eq (Δ : ℝ) :
    crystalFieldOrbitalTorque Δ = (2 * (Δ : ℂ)) • InternalSpace.pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crystalFieldOrbitalTorque, crystalFieldHamiltonian, orbitalZ,
      InternalSpace.pauliX, InternalSpace.pauliY, InternalSpace.pauliZ] <;> ring_nf <;> simp [pow_two, Complex.I_mul_I]

/-- The crystal-field torque is nonzero in a concrete two-orbital site. -/
theorem crystalFieldOrbitalTorque_one_ne_zero :
    crystalFieldOrbitalTorque 1 ≠ 0 := by
  intro h
  rw [crystalFieldOrbitalTorque_eq] at h
  have h01 := congrArg (fun M : InternalSpace.PauliMatrix => M 0 1) h
  norm_num [InternalSpace.pauliX] at h01

/-- On a closed singleton lattice, no antisymmetric bond flux can reproduce
the nonvanishing local crystal-field torque. -/
theorem singleton_crystalFieldOrbitalTorque_not_bondFlux :
    ¬ ∃ J : Fin 1 → Fin 1 → InternalSpace.PauliMatrix,
      (∀ x y, J x y = -J y x) ∧
        (∀ x, crystalFieldOrbitalTorque 1 = ∑ y : Fin 1, J x y) := by
  rintro ⟨J, hantisym, hbalance⟩
  have hdiag (x : Fin 1) : J x x = 0 := by
    have htwo : (2 : ℂ) • J x x = 0 := by
      calc
        (2 : ℂ) • J x x = J x x + J x x := two_smul ℂ _
        _ = J x x + -J x x := congrArg (fun z => J x x + z) (hantisym x x)
        _ = 0 := add_neg_cancel _
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  apply crystalFieldOrbitalTorque_one_ne_zero
  calc
    crystalFieldOrbitalTorque 1 = ∑ x : Fin 1, ∑ y : Fin 1, J x y := by
      simpa using hbalance (0 : Fin 1)
    _ = 0 := Combinatorics.sum_antisymmetric_eq_zero J hantisym hdiag

end QuantumTheory.Models.OrbitalTransport
