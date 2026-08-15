import LeanCondensedMatter.SecondQuantization.Fermionic.Validation.TwoSiteDimerLehmann

set_option linter.style.header false

/-!
# Operator-to-spectral bridge for the two-site dimer

The exact conductivity benchmark in `TwoSiteDimerLehmann` records the two one-particle energies
and current transition coefficients as scalar finite-table input.  This module derives those
coefficients from the bounded full-Fock dimer Hamiltonian and continuity-derived bond current.

Inside the full finite-lattice fermionic Fock space, let `|0⟩` and `|1⟩` denote the one-particle
occupation basis states.  For unit hopping, the unnormalized energy eigenvectors are

```text
|−⟩ = |0⟩ - |1⟩,
|+⟩ = |0⟩ + |1⟩.
```

They obey

```text
H |−⟩ = -|−⟩,        H |+⟩ = |+⟩,
J |+⟩ =  i |−⟩,      J |−⟩ = -i |+⟩.
```

A common nonzero normalization of `|−⟩` and `|+⟩` preserves these transition coefficients, so these
identities supply the operator origin of the `(-1,+1)` energies and `±i` current entries used by
the exact finite Lehmann table.  No diagonalization oracle or floating-point calculation is used.
-/

namespace SecondQuantization
namespace Fermionic
namespace Validation

open Lattice Transport

noncomputable section

/-- One-particle site basis state embedded in the full two-site finite Hilbert Fock space. -/
noncomputable def twoSiteDimerSiteState (i : TwoSite) : TwoSiteHilbertFock :=
  Common.finiteHilbertBasisState ({i} : Occupation TwoSite)

/-- Lower-energy unit-hopping dimer eigenvector before normalization. -/
noncomputable def twoSiteDimerBondingState : TwoSiteHilbertFock :=
  twoSiteDimerSiteState 0 - twoSiteDimerSiteState 1

/-- Upper-energy unit-hopping dimer eigenvector before normalization. -/
noncomputable def twoSiteDimerAntibondingState : TwoSiteHilbertFock :=
  twoSiteDimerSiteState 0 + twoSiteDimerSiteState 1

/-- Unit hopping exchanges the two one-particle site states. -/
@[simp]
theorem twoSiteDimerHamiltonian_one_apply_site_zero :
    twoSiteDimerHamiltonian 1 (twoSiteDimerSiteState 0) =
      twoSiteDimerSiteState 1 := by
  simp [twoSiteDimerHamiltonian, twoSiteDimerSiteState]

/-- Unit hopping exchanges the two one-particle site states. -/
@[simp]
theorem twoSiteDimerHamiltonian_one_apply_site_one :
    twoSiteDimerHamiltonian 1 (twoSiteDimerSiteState 1) =
      twoSiteDimerSiteState 0 := by
  simp [twoSiteDimerHamiltonian, twoSiteDimerSiteState]

/-- The antisymmetric one-particle state has energy `-1` for the repository's positive-hopping
sign convention. -/
theorem twoSiteDimerHamiltonian_one_apply_bonding :
    twoSiteDimerHamiltonian 1 twoSiteDimerBondingState =
      (-1 : ℂ) • twoSiteDimerBondingState := by
  rw [twoSiteDimerBondingState, map_sub,
    twoSiteDimerHamiltonian_one_apply_site_zero,
    twoSiteDimerHamiltonian_one_apply_site_one]
  simp [sub_eq_add_neg, add_comm]

/-- The symmetric one-particle state has energy `+1`. -/
theorem twoSiteDimerHamiltonian_one_apply_antibonding :
    twoSiteDimerHamiltonian 1 twoSiteDimerAntibondingState =
      (1 : ℂ) • twoSiteDimerAntibondingState := by
  rw [twoSiteDimerAntibondingState, map_add,
    twoSiteDimerHamiltonian_one_apply_site_zero,
    twoSiteDimerHamiltonian_one_apply_site_one]
  simp [add_comm]

/-- At `t = ℏ = q = 1`, the continuity-derived current is
`i (|0⟩⟨1| - |1⟩⟨0|)` after second quantization and bounded transport. -/
theorem twoSiteDimerCurrent_one_eq_matrixUnits :
    twoSiteDimerCurrent 1 =
      Complex.I •
        (boundedDgammaMatrixUnit (0 : TwoSite) 1 -
          boundedDgammaMatrixUnit (1 : TwoSite) 0) := by
  unfold twoSiteDimerCurrent
  rw [boundedBondCurrent_eq_peierlsCoupling_smul]
  rw [LocallyFiniteHopping.boundedBondOperator_eq]
  norm_num [peierlsCoupling, LocallyFiniteHopping.amplitude_eq]

/-- The oriented unit current sends `|0⟩` to `-i |1⟩`. -/
@[simp]
theorem twoSiteDimerCurrent_one_apply_site_zero :
    twoSiteDimerCurrent 1 (twoSiteDimerSiteState 0) =
      (-Complex.I) • twoSiteDimerSiteState 1 := by
  rw [twoSiteDimerCurrent_one_eq_matrixUnits]
  simp [twoSiteDimerSiteState, smul_sub, neg_smul]

/-- The oriented unit current sends `|1⟩` to `i |0⟩`. -/
@[simp]
theorem twoSiteDimerCurrent_one_apply_site_one :
    twoSiteDimerCurrent 1 (twoSiteDimerSiteState 1) =
      Complex.I • twoSiteDimerSiteState 0 := by
  rw [twoSiteDimerCurrent_one_eq_matrixUnits]
  simp [twoSiteDimerSiteState, smul_sub]

/-- The current takes the upper state to `i` times the lower state. -/
theorem twoSiteDimerCurrent_one_apply_antibonding :
    twoSiteDimerCurrent 1 twoSiteDimerAntibondingState =
      Complex.I • twoSiteDimerBondingState := by
  rw [twoSiteDimerAntibondingState, map_add,
    twoSiteDimerCurrent_one_apply_site_zero,
    twoSiteDimerCurrent_one_apply_site_one,
    twoSiteDimerBondingState, smul_sub]
  simp [neg_smul, sub_eq_add_neg, add_comm]

/-- The current takes the lower state to `-i` times the upper state. -/
theorem twoSiteDimerCurrent_one_apply_bonding :
    twoSiteDimerCurrent 1 twoSiteDimerBondingState =
      (-Complex.I) • twoSiteDimerAntibondingState := by
  rw [twoSiteDimerBondingState, map_sub,
    twoSiteDimerCurrent_one_apply_site_zero,
    twoSiteDimerCurrent_one_apply_site_one,
    twoSiteDimerAntibondingState, smul_add]
  simp [neg_smul, sub_eq_add_neg, add_comm]

/-- The lower scalar-table energy is exactly the eigenvalue derived from the bounded Hamiltonian. -/
theorem twoSiteDimerTable_groundEnergy_from_operator :
    twoSiteDimerHamiltonian 1 twoSiteDimerBondingState =
      (twoSiteDimerGroundStateLehmannTable.energy 0 : ℂ) • twoSiteDimerBondingState := by
  rw [twoSiteDimerGroundStateLehmannTable_energy_zero]
  simpa using twoSiteDimerHamiltonian_one_apply_bonding

/-- The upper scalar-table energy is exactly the eigenvalue derived from the bounded Hamiltonian. -/
theorem twoSiteDimerTable_excitedEnergy_from_operator :
    twoSiteDimerHamiltonian 1 twoSiteDimerAntibondingState =
      (twoSiteDimerGroundStateLehmannTable.energy 1 : ℂ) • twoSiteDimerAntibondingState := by
  rw [twoSiteDimerGroundStateLehmannTable_energy_one]
  simpa using twoSiteDimerHamiltonian_one_apply_antibonding

/-- The table entry `J₋₊ = i` is the transition coefficient of the bounded current. -/
theorem twoSiteDimerTable_current_zero_one_from_operator :
    twoSiteDimerCurrent 1 twoSiteDimerAntibondingState =
      twoSiteDimerGroundStateLehmannTable.matrixA 0 1 • twoSiteDimerBondingState := by
  change twoSiteDimerCurrent 1 twoSiteDimerAntibondingState =
    twoSiteDimerEnergyBasisCurrent 0 1 • twoSiteDimerBondingState
  rw [twoSiteDimerEnergyBasisCurrent_zero_one]
  exact twoSiteDimerCurrent_one_apply_antibonding

/-- The table entry `J₊₋ = -i` is the reverse transition coefficient of the bounded current. -/
theorem twoSiteDimerTable_current_one_zero_from_operator :
    twoSiteDimerCurrent 1 twoSiteDimerBondingState =
      twoSiteDimerGroundStateLehmannTable.matrixA 1 0 • twoSiteDimerAntibondingState := by
  change twoSiteDimerCurrent 1 twoSiteDimerBondingState =
    twoSiteDimerEnergyBasisCurrent 1 0 • twoSiteDimerAntibondingState
  rw [twoSiteDimerEnergyBasisCurrent_one_zero]
  exact twoSiteDimerCurrent_one_apply_bonding

end
end Validation
end Fermionic
end SecondQuantization
