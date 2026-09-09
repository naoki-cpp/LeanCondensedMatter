import LeanCondensedMatter.SecondQuantization.Fermionic.Validation.TwoSiteDimerFrequency
import LeanCondensedMatter.SecondQuantization.Fermionic.Validation.TwoSiteDimerOperatorBridge
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Gapped two-site conductivity benchmark

This module adds an onsite-imbalanced two-site model to the exact finite-conductivity validation
stack. Starting from the existing hopping dimer, add the one-particle diagonal term

```text
Δ (|0⟩⟨0| - |1⟩⟨1|).
```

At unit hopping and `Δ = 3/4`, the one-particle Hamiltonian is

```text
[[ 3/4, 1   ],
 [ 1,  -3/4 ]]
```

with exact eigenvalues `(-5/4,+5/4)` and unnormalized eigenvectors `(1,-2)` and `(2,1)`.
The same Peierls bond current has transition coefficients `±i`, while the occupied-state Peierls
contact expectation is `-4/5`. At the fixed-rate point `ω = 0`, `η = 1`, the direct two-level
Lehmann response is `20/29` and the canonical finite conductivity is `16/145`.

No zero-broadening, DC, thermodynamic, disorder, or numerical limit is taken.
-/

namespace SecondQuantization
namespace Fermionic
namespace Validation

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse QuantumTheory.Transport
open Transport

noncomputable section

/-- Two-site hopping Hamiltonian with an additional real onsite imbalance `±gap`. -/
noncomputable def twoSiteGappedHamiltonian (t : ℂ) (gap : ℝ) :
    TwoSiteHilbertFock →L[ℂ] TwoSiteHilbertFock :=
  twoSiteDimerHamiltonian t +
    (gap : ℂ) •
      (boundedDgammaMatrixUnit (0 : TwoSite) 0 -
        boundedDgammaMatrixUnit (1 : TwoSite) 1)

@[simp]
theorem twoSiteGappedHamiltonian_apply_site_zero (t : ℂ) (gap : ℝ) :
    twoSiteGappedHamiltonian t gap (twoSiteDimerSiteState 0) =
      (gap : ℂ) • twoSiteDimerSiteState 0 + t • twoSiteDimerSiteState 1 := by
  simp [twoSiteGappedHamiltonian, twoSiteDimerHamiltonian, twoSiteDimerSiteState,
    add_comm]

@[simp]
theorem twoSiteGappedHamiltonian_apply_site_one (t : ℂ) (gap : ℝ) :
    twoSiteGappedHamiltonian t gap (twoSiteDimerSiteState 1) =
      star t • twoSiteDimerSiteState 0 - (gap : ℂ) • twoSiteDimerSiteState 1 := by
  simp [twoSiteGappedHamiltonian, twoSiteDimerHamiltonian, twoSiteDimerSiteState,
    sub_eq_add_neg, add_comm]

/-- Lower eigenstate of the exact benchmark before normalization. -/
noncomputable def twoSiteGappedBenchmarkGroundState : TwoSiteHilbertFock :=
  twoSiteDimerSiteState 0 - (2 : ℂ) • twoSiteDimerSiteState 1

/-- Upper eigenstate of the exact benchmark before normalization. -/
noncomputable def twoSiteGappedBenchmarkExcitedState : TwoSiteHilbertFock :=
  (2 : ℂ) • twoSiteDimerSiteState 0 + twoSiteDimerSiteState 1

/-- The benchmark Hamiltonian at unit hopping and onsite imbalance `3/4` has lower energy `-5/4`. -/
theorem twoSiteGappedBenchmark_ground_eigenvector :
    twoSiteGappedHamiltonian 1 (3 / 4) twoSiteGappedBenchmarkGroundState =
      ((-5 : ℂ) / 4) • twoSiteGappedBenchmarkGroundState := by
  rw [twoSiteGappedBenchmarkGroundState, map_sub, map_smul,
    twoSiteGappedHamiltonian_apply_site_zero,
    twoSiteGappedHamiltonian_apply_site_one]
  norm_num
  module

/-- The benchmark Hamiltonian at unit hopping and onsite imbalance `3/4` has upper energy `5/4`. -/
theorem twoSiteGappedBenchmark_excited_eigenvector :
    twoSiteGappedHamiltonian 1 (3 / 4) twoSiteGappedBenchmarkExcitedState =
      ((5 : ℂ) / 4) • twoSiteGappedBenchmarkExcitedState := by
  rw [twoSiteGappedBenchmarkExcitedState, map_add, map_smul,
    twoSiteGappedHamiltonian_apply_site_zero,
    twoSiteGappedHamiltonian_apply_site_one]
  norm_num
  module

/-- The physical unit-hopping Peierls current maps the upper benchmark state to `i` times the lower
state despite the onsite imbalance. -/
theorem twoSiteGappedBenchmark_current_apply_excited :
    twoSiteDimerCurrent 1 twoSiteGappedBenchmarkExcitedState =
      Complex.I • twoSiteGappedBenchmarkGroundState := by
  rw [twoSiteGappedBenchmarkExcitedState, map_add, map_smul,
    twoSiteDimerCurrent_one_apply_site_zero,
    twoSiteDimerCurrent_one_apply_site_one,
    twoSiteGappedBenchmarkGroundState]
  module

/-- The reverse current transition has coefficient `-i`. -/
theorem twoSiteGappedBenchmark_current_apply_ground :
    twoSiteDimerCurrent 1 twoSiteGappedBenchmarkGroundState =
      (-Complex.I) • twoSiteGappedBenchmarkExcitedState := by
  rw [twoSiteGappedBenchmarkGroundState, map_sub, map_smul,
    twoSiteDimerCurrent_one_apply_site_zero,
    twoSiteDimerCurrent_one_apply_site_one,
    twoSiteGappedBenchmarkExcitedState]
  module

/-- In the benchmark energy basis the Peierls contact has occupied-state diagonal coefficient
`-4/5`; the remaining `-3/5` coefficient mixes into the upper state. -/
theorem twoSiteGappedBenchmark_contact_decomposition :
    twoSiteDimerContact 1 twoSiteGappedBenchmarkGroundState =
      ((-4 : ℂ) / 5) • twoSiteGappedBenchmarkGroundState +
        ((-3 : ℂ) / 5) • twoSiteGappedBenchmarkExcitedState := by
  rw [twoSiteDimerContact_one_eq_hamiltonian,
    twoSiteGappedBenchmarkGroundState, map_sub, map_smul,
    twoSiteDimerHamiltonian_one_apply_site_zero,
    twoSiteDimerHamiltonian_one_apply_site_one,
    twoSiteGappedBenchmarkExcitedState]
  module

private theorem inner_twoSiteDimerSiteState (i j : TwoSite) :
    inner ℂ (twoSiteDimerSiteState i) (twoSiteDimerSiteState j) =
      if i = j then 1 else 0 := by
  unfold twoSiteDimerSiteState
  simpa using
    (orthonormal_iff_ite.mp
      (Common.finiteHilbertOrthonormalBasis
        (Config := Occupation TwoSite)).orthonormal
      ({i} : Occupation TwoSite) ({j} : Occupation TwoSite))

@[simp]
theorem twoSiteGappedBenchmark_ground_inner_excited :
    inner ℂ twoSiteGappedBenchmarkGroundState twoSiteGappedBenchmarkExcitedState = 0 := by
  rw [twoSiteGappedBenchmarkGroundState, twoSiteGappedBenchmarkExcitedState]
  simp only [inner_sub_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [inner_twoSiteDimerSiteState 0 0, inner_twoSiteDimerSiteState 0 1,
    inner_twoSiteDimerSiteState 1 0, inner_twoSiteDimerSiteState 1 1]
  norm_num

@[simp]
theorem twoSiteGappedBenchmark_ground_norm_sq :
    inner ℂ twoSiteGappedBenchmarkGroundState twoSiteGappedBenchmarkGroundState = 5 := by
  rw [twoSiteGappedBenchmarkGroundState]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  rw [inner_twoSiteDimerSiteState 0 0, inner_twoSiteDimerSiteState 0 1,
    inner_twoSiteDimerSiteState 1 0, inner_twoSiteDimerSiteState 1 1]
  norm_num

/-- The normalized ground-state contact expectation is exactly `-4/5`, derived from the concrete
Peierls contact rather than inserted independently. -/
theorem twoSiteGappedBenchmark_contactExpectation :
    inner ℂ twoSiteGappedBenchmarkGroundState
        (twoSiteDimerContact 1 twoSiteGappedBenchmarkGroundState) /
      inner ℂ twoSiteGappedBenchmarkGroundState twoSiteGappedBenchmarkGroundState =
        (-4 : ℂ) / 5 := by
  rw [twoSiteGappedBenchmark_contact_decomposition]
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    twoSiteGappedBenchmark_ground_norm_sq,
    twoSiteGappedBenchmark_ground_inner_excited]
  norm_num

/-- Exact scalar Lehmann data for the gapped benchmark in its two-state energy basis. -/
def twoSiteGappedBenchmarkLehmannTable : FiniteLehmannTable (Fin 2) where
  energy := fun n => if n = 0 then -5 / 4 else 5 / 4
  probability := fun n => if n = 0 then 1 else 0
  matrixA := twoSiteDimerEnergyBasisCurrent
  matrixB := twoSiteDimerEnergyBasisCurrent

/-- Complete canonical finite-conductivity input for the gapped benchmark. -/
def twoSiteGappedBenchmarkConductivityTable : FiniteConductivityTable (Fin 2) where
  lehmann := twoSiteGappedBenchmarkLehmannTable
  contact := (-4 : ℂ) / 5

@[simp]
theorem twoSiteGappedBenchmarkLehmannTable_energy_zero :
    twoSiteGappedBenchmarkLehmannTable.energy 0 = -5 / 4 := by
  norm_num [twoSiteGappedBenchmarkLehmannTable]

@[simp]
theorem twoSiteGappedBenchmarkLehmannTable_energy_one :
    twoSiteGappedBenchmarkLehmannTable.energy 1 = 5 / 4 := by
  norm_num [twoSiteGappedBenchmarkLehmannTable]

@[simp]
theorem twoSiteGappedBenchmarkTransitionWeight_zero_one :
    finiteLehmannTableTransitionWeight 1
        twoSiteGappedBenchmarkLehmannTable (0, 1) = Complex.I := by
  norm_num [finiteLehmannTableTransitionWeight, twoSiteGappedBenchmarkLehmannTable,
    twoSiteDimerEnergyBasisCurrent]

@[simp]
theorem twoSiteGappedBenchmarkTransitionWeight_one_zero :
    finiteLehmannTableTransitionWeight 1
        twoSiteGappedBenchmarkLehmannTable (1, 0) = -Complex.I := by
  norm_num [finiteLehmannTableTransitionWeight, twoSiteGappedBenchmarkLehmannTable,
    twoSiteDimerEnergyBasisCurrent]

/-- The lower table energy is the operator-derived lower eigenvalue. -/
theorem twoSiteGappedBenchmarkTable_groundEnergy_from_operator :
    twoSiteGappedHamiltonian 1 (3 / 4) twoSiteGappedBenchmarkGroundState =
      (twoSiteGappedBenchmarkLehmannTable.energy 0 : ℂ) •
        twoSiteGappedBenchmarkGroundState := by
  rw [twoSiteGappedBenchmarkLehmannTable_energy_zero]
  convert twoSiteGappedBenchmark_ground_eigenvector using 1 <;> norm_num

/-- The upper table energy is the operator-derived upper eigenvalue. -/
theorem twoSiteGappedBenchmarkTable_excitedEnergy_from_operator :
    twoSiteGappedHamiltonian 1 (3 / 4) twoSiteGappedBenchmarkExcitedState =
      (twoSiteGappedBenchmarkLehmannTable.energy 1 : ℂ) •
        twoSiteGappedBenchmarkExcitedState := by
  rw [twoSiteGappedBenchmarkLehmannTable_energy_one]
  convert twoSiteGappedBenchmark_excited_eigenvector using 1 <;> norm_num

/-- The table entry `J₋₊ = i` is the concrete Peierls-current transition coefficient. -/
theorem twoSiteGappedBenchmarkTable_current_zero_one_from_operator :
    twoSiteDimerCurrent 1 twoSiteGappedBenchmarkExcitedState =
      twoSiteGappedBenchmarkLehmannTable.matrixA 0 1 •
        twoSiteGappedBenchmarkGroundState := by
  change twoSiteDimerCurrent 1 twoSiteGappedBenchmarkExcitedState =
    twoSiteDimerEnergyBasisCurrent 0 1 • twoSiteGappedBenchmarkGroundState
  rw [twoSiteDimerEnergyBasisCurrent_zero_one]
  exact twoSiteGappedBenchmark_current_apply_excited

/-- The reverse table current entry is likewise operator-derived. -/
theorem twoSiteGappedBenchmarkTable_current_one_zero_from_operator :
    twoSiteDimerCurrent 1 twoSiteGappedBenchmarkGroundState =
      twoSiteGappedBenchmarkLehmannTable.matrixA 1 0 •
        twoSiteGappedBenchmarkExcitedState := by
  change twoSiteDimerCurrent 1 twoSiteGappedBenchmarkGroundState =
    twoSiteDimerEnergyBasisCurrent 1 0 • twoSiteGappedBenchmarkExcitedState
  rw [twoSiteDimerEnergyBasisCurrent_one_zero]
  exact twoSiteGappedBenchmark_current_apply_ground

/-- The scalar-table contact is the normalized expectation derived from the concrete Peierls contact. -/
theorem twoSiteGappedBenchmarkTable_contact_from_operator :
    inner ℂ twoSiteGappedBenchmarkGroundState
        (twoSiteDimerContact 1 twoSiteGappedBenchmarkGroundState) /
      inner ℂ twoSiteGappedBenchmarkGroundState twoSiteGappedBenchmarkGroundState =
        twoSiteGappedBenchmarkConductivityTable.contact := by
  change _ = (-4 : ℂ) / 5
  exact twoSiteGappedBenchmark_contactExpectation

/-- Direct two-level Lehmann evaluation at the exact fixed-rate benchmark point. -/
theorem twoSiteGappedBenchmark_lehmannResponse_zero_one :
    finiteLehmannTableResponse 1 0 1 twoSiteGappedBenchmarkLehmannTable =
      (20 : ℂ) / 29 := by
  classical
  unfold finiteLehmannTableResponse
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.isValue,
    twoSiteGappedBenchmarkLehmannTable_energy_zero,
    twoSiteGappedBenchmarkLehmannTable_energy_one,
    twoSiteGappedBenchmarkTransitionWeight_zero_one,
    twoSiteGappedBenchmarkTransitionWeight_one_zero,
    finiteLehmannTableTransitionWeight_diag, sub_self]
  apply Complex.ext <;>
    norm_num [lehmannTerm, lehmannDenominator, Complex.normSq]

/-- Exact nonzero-gap, nonzero-hopping conductivity benchmark at `ω = 0`, `η = 1`. -/
theorem twoSiteGappedBenchmark_conductivity_zero_one :
    finiteConductivityTableValue twoSiteDimerUnitVolume 1 0 1
        twoSiteGappedBenchmarkConductivityTable = (16 : ℂ) / 145 := by
  unfold finiteConductivityTableValue
  change
    (finiteLehmannTableResponse 1 0 1 twoSiteGappedBenchmarkLehmannTable +
        ((-4 : ℂ) / 5)) *
      finiteVolumeConductivityNormalization twoSiteDimerUnitVolume 0 1 = (16 : ℂ) / 145
  rw [twoSiteGappedBenchmark_lehmannResponse_zero_one,
    twoSiteDimerUnitVolume_normalization_zero_one]
  norm_num

end
end Validation
end Fermionic
end SecondQuantization
