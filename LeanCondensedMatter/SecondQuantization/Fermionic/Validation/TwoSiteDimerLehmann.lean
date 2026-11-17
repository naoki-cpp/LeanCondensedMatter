import LeanCondensedMatter.Transport.FiniteConductivityTable
import LeanCondensedMatter.SecondQuantization.Fermionic.Validation.TwoSiteDimer

set_option linter.style.header false

/-!
# Exact Lehmann and conductivity benchmark for the two-site dimer

This module records the spectral data of the one-particle sector of the unit-hopping two-site dimer
in its bonding/antibonding energy basis. With `ℏ = 1`, the energies are `-1` and `+1`; the
zero-temperature ground-state occupation is `(1,0)`; and the continuity-derived oriented current
has off-diagonal matrix elements `i` and `-i` in this basis.

At the explicit regularized point `ω = 0`, `η = 1`, the finite Lehmann current-current response is
exactly `4/5`. For unit hopping and unit charge, the Peierls contact operator restricted to this
one-particle sector equals the hopping Hamiltonian, so its ground-state expectation is `-1`.
With unit physical volume, the existing vector-potential-to-electric-field normalization is `-1`,
and the resulting finite conductivity is therefore exactly `1/5`.

No floating-point approximation, zero-broadening limit, DC limit, or thermodynamic limit occurs
here. The table evaluator and normalization are the same public definitions used by the proved
finite Kubo-Greenwood chain.
-/

namespace SecondQuantization
namespace Fermionic
namespace Validation

open QuantumTheory.LinearResponse
open QuantumTheory.Transport
open Transport

noncomputable section

/-- Current matrix elements of the unit-hopping dimer in the ordered energy basis
`(|bonding⟩, |antibonding⟩)` with energies `(-1,+1)`.

The diagonal elements vanish, while `J₋₊ = i` and `J₊₋ = -i`. -/
def twoSiteDimerEnergyBasisCurrent (m n : Fin 2) : ℂ :=
  if m = n then 0 else if m = 0 then Complex.I else -Complex.I

/-- Scalar Lehmann data for the one-particle sector of the unit-hopping two-site dimer in its
energy basis, with the lower level fully occupied and the upper level empty. -/
def twoSiteDimerGroundStateLehmannTable : FiniteLehmannTable (Fin 2) where
  energy := fun n => if n = 0 then -1 else 1
  probability := fun n => if n = 0 then 1 else 0
  matrixA := twoSiteDimerEnergyBasisCurrent
  matrixB := twoSiteDimerEnergyBasisCurrent

/-- Unit positive physical volume used by the exact benchmark. -/
def twoSiteDimerUnitVolume : PositiveVolume where
  volume := 1
  volume_pos := by norm_num

/-- Complete scalar conductivity input for the unit-hopping one-particle dimer ground state.

The contact value `-1` is the ground-state expectation of the unit-hopping Peierls contact, which
coincides with the hopping Hamiltonian in this sector. -/
def twoSiteDimerGroundStateConductivityTable : FiniteConductivityTable (Fin 2) where
  lehmann := twoSiteDimerGroundStateLehmannTable
  contact := -1

@[simp]
theorem twoSiteDimerGroundStateLehmannTable_energy_zero :
    twoSiteDimerGroundStateLehmannTable.energy 0 = -1 := by
  simp [twoSiteDimerGroundStateLehmannTable]

@[simp]
theorem twoSiteDimerGroundStateLehmannTable_energy_one :
    twoSiteDimerGroundStateLehmannTable.energy 1 = 1 := by
  simp [twoSiteDimerGroundStateLehmannTable]

@[simp]
theorem twoSiteDimerGroundStateLehmannTable_probability_zero :
    twoSiteDimerGroundStateLehmannTable.probability 0 = 1 := by
  simp [twoSiteDimerGroundStateLehmannTable]

@[simp]
theorem twoSiteDimerGroundStateLehmannTable_probability_one :
    twoSiteDimerGroundStateLehmannTable.probability 1 = 0 := by
  simp [twoSiteDimerGroundStateLehmannTable]

@[simp]
theorem twoSiteDimerEnergyBasisCurrent_zero_zero :
    twoSiteDimerEnergyBasisCurrent 0 0 = 0 := by
  simp [twoSiteDimerEnergyBasisCurrent]

@[simp]
theorem twoSiteDimerEnergyBasisCurrent_one_one :
    twoSiteDimerEnergyBasisCurrent 1 1 = 0 := by
  simp [twoSiteDimerEnergyBasisCurrent]

@[simp]
theorem twoSiteDimerEnergyBasisCurrent_zero_one :
    twoSiteDimerEnergyBasisCurrent 0 1 = Complex.I := by
  simp [twoSiteDimerEnergyBasisCurrent]

@[simp]
theorem twoSiteDimerEnergyBasisCurrent_one_zero :
    twoSiteDimerEnergyBasisCurrent 1 0 = -Complex.I := by
  simp [twoSiteDimerEnergyBasisCurrent]

@[simp]
theorem twoSiteDimerGroundStateTransitionWeight_zero_one :
    (finiteLehmannTableTransitionData 1
        twoSiteDimerGroundStateLehmannTable (0, 1)).weight = Complex.I := by
  norm_num [finiteLehmannTableTransitionData,
    orderedLehmannTransitionWeight, twoSiteDimerGroundStateLehmannTable,
    twoSiteDimerEnergyBasisCurrent]

@[simp]
theorem twoSiteDimerGroundStateTransitionWeight_one_zero :
    (finiteLehmannTableTransitionData 1
        twoSiteDimerGroundStateLehmannTable (1, 0)).weight = -Complex.I := by
  norm_num [finiteLehmannTableTransitionData,
    orderedLehmannTransitionWeight, twoSiteDimerGroundStateLehmannTable,
    twoSiteDimerEnergyBasisCurrent]

/-- The exact fixed-rate response of two opposite unit-current transitions separated
by the real energy gap `Δ`. The response depends only on the level spacing. -/
private theorem twoLevelLehmannPair (Δ : ℝ) :
    lehmannTerm 1 0 1 (-Δ) Complex.I +
      lehmannTerm 1 0 1 Δ (-Complex.I) =
        ((2 * Δ / (1 + Δ ^ 2) : ℝ) : ℂ) := by
  have hp : (1 : ℂ) + Complex.I * (Δ : ℂ) ≠ 0 := by
    simpa [lehmannDenominator] using
      (lehmannDenominator_ne_zero 1 0 1 (-Δ) (by norm_num))
  have hm : (1 : ℂ) - Complex.I * (Δ : ℂ) ≠ 0 := by
    simpa [lehmannDenominator] using
      (lehmannDenominator_ne_zero 1 0 1 Δ (by norm_num))
  have hd : (1 : ℂ) + (Δ : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) + Δ ^ 2 ≠ 0 by positivity)
  have halgebra :
      Complex.I * ((1 : ℂ) + Complex.I * (Δ : ℂ))⁻¹ -
        Complex.I * ((1 : ℂ) - Complex.I * (Δ : ℂ))⁻¹ =
          (2 * (Δ : ℂ)) / (1 + (Δ : ℂ) ^ 2) := by
    field_simp [hp, hm, hd]
    ring_nf
    simp [Complex.I_sq]
  convert halgebra using 1 <;>
    simp [lehmannTerm, lehmannDenominator, div_eq_mul_inv, sub_eq_add_neg]

/-- For a two-level Lehmann table with opposite unit-current transition weights,
the response is fixed by its real level spacing `Δ = E₁ - E₀`. -/
theorem twoLevelLehmannResponse_of_gap (table : FiniteLehmannTable (Fin 2)) (Δ : ℝ)
    (hgap : table.energy 1 - table.energy 0 = Δ)
    (h01 : (finiteLehmannTableTransitionData 1 table (0, 1)).weight = Complex.I)
    (h10 : (finiteLehmannTableTransitionData 1 table (1, 0)).weight = -Complex.I) :
    finiteLehmannTableResponse 1 0 1 table =
      ((2 * Δ / (1 + Δ ^ 2) : ℝ) : ℂ) := by
  classical
  have hrev : table.energy 0 - table.energy 1 = -Δ := by linarith
  unfold finiteLehmannTableResponse
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.isValue, LehmannTransitionData.frequencyTerm,
    finiteLehmannTableTransitionData_energyGap,
    finiteLehmannTableTransitionData_weight_diag, sub_self]
  simp only [lehmannTerm, zero_mul, add_zero, zero_add]
  rw [h01, h10]
  simp only [orderedLehmannEnergyGap]
  rw [hrev, hgap]
  simpa only [lehmannTerm, neg_mul, neg_add_rev] using twoLevelLehmannPair Δ

/-- At `ℏ = 1`, zero driving frequency, and positive switching rate `η = 1`, the dimer's exact
finite Lehmann current-current response is `4/5`. -/
theorem twoSiteDimerGroundState_lehmannResponse_zero_one :
    finiteLehmannTableResponse 1 0 1 twoSiteDimerGroundStateLehmannTable =
      (4 : ℂ) / 5 := by
  convert twoLevelLehmannResponse_of_gap twoSiteDimerGroundStateLehmannTable 2
    (by norm_num [twoSiteDimerGroundStateLehmannTable])
    twoSiteDimerGroundStateTransitionWeight_zero_one
    twoSiteDimerGroundStateTransitionWeight_one_zero using 1; norm_num

/-- The benchmark contact expectation equals the occupied bonding-state energy. -/
theorem twoSiteDimerGroundState_contact_eq_groundEnergy :
    twoSiteDimerGroundStateConductivityTable.contact =
      twoSiteDimerGroundStateConductivityTable.lehmann.energy 0 := by
  norm_num [twoSiteDimerGroundStateConductivityTable,
    twoSiteDimerGroundStateLehmannTable]

/-- At unit volume, zero frequency, and `η = 1`, the repository's finite-volume electric-field
normalization is exactly `-1`. -/
theorem twoSiteDimerUnitVolume_normalization_zero_one :
    finiteVolumeConductivityNormalization twoSiteDimerUnitVolume 0 1 = -1 := by
  norm_num [finiteVolumeConductivityNormalization, adiabaticElectricFieldFactor,
    twoSiteDimerUnitVolume]

/-- First exact end-to-end scalar electrical-conductivity benchmark:

`current-current = 4/5`, `contact = -1`, and the unit-volume electric-field normalization is `-1`,
so the fixed-rate conductivity at `ℏ = 1`, `ω = 0`, `η = 1` is exactly `1/5`. -/
theorem twoSiteDimerGroundState_conductivity_zero_one :
    finiteConductivityTableValue twoSiteDimerUnitVolume 1 0 1
        twoSiteDimerGroundStateConductivityTable = (1 : ℂ) / 5 := by
  unfold finiteConductivityTableValue
  change
    (finiteLehmannTableResponse 1 0 1 twoSiteDimerGroundStateLehmannTable + (-1 : ℂ)) *
        finiteVolumeConductivityNormalization twoSiteDimerUnitVolume 0 1 = (1 : ℂ) / 5
  rw [twoSiteDimerGroundState_lehmannResponse_zero_one,
    twoSiteDimerUnitVolume_normalization_zero_one]
  norm_num

end
end Validation
end Fermionic
end SecondQuantization
