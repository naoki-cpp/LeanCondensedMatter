import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Transition
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Free
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option linter.style.header false

/-! # Eigenbasis operator realization of Lehmann transitions -/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Spectral data in an energy eigenbasis for a bounded free system and a diagonal normalized state.

The basis vectors diagonalize `system.hamiltonian`; `probability` gives the corresponding diagonal
state weights. The index type may be infinite. -/
structure EnergyEigenbasisLehmannData
    (system : BoundedFreeSystem H) (ι : Type*) where
  /-- Hilbert basis of energy eigenvectors. -/
  basis : HilbertBasis ι ℂ H
  /-- Energy assigned to each basis vector. -/
  energy : ι → ℝ
  hamiltonian_apply_basis : ∀ i,
    system.hamiltonian.1 (basis i) = (energy i : ℂ) • basis i
  /-- Normalized diagonal probability assigned to each basis vector. -/
  probability : ι → ℝ
  probability_nonneg : ∀ i, 0 ≤ probability i
  probability_hasSum : HasSum probability 1

/-- In finite dimension the spectral theorem supplies an actual normalized
eigenbasis state with all probability on a selected eigenvector. No
nondegeneracy or supplied eigenbasis is required. -/
noncomputable def EnergyEigenbasisLehmannData.ofSingleOccupied
    [FiniteDimensional ℂ H] (system : BoundedFreeSystem H)
    (occupied : Fin (Module.finrank ℂ H)) :
    EnergyEigenbasisLehmannData system (Fin (Module.finrank ℂ H)) where
  basis := (system.hamiltonian.2.isSymmetric.eigenvectorBasis rfl).toHilbertBasis
  energy := system.hamiltonian.2.isSymmetric.eigenvalues rfl
  hamiltonian_apply_basis := by
    intro i
    simp only [OrthonormalBasis.coe_toHilbertBasis]
    exact system.hamiltonian.2.isSymmetric.apply_eigenvectorBasis rfl i
  probability := fun i => if i = occupied then 1 else 0
  probability_nonneg := by
    intro i
    split <;> norm_num
  probability_hasSum := by
    have h := (Summable.of_finite
      (f := fun i : Fin (Module.finrank ℂ H) => if i = occupied then (1 : ℝ) else 0)).hasSum
    simpa [tsum_fintype] using h

variable {ι : Type*} (system : BoundedFreeSystem H)

/-- Adapt one operator-level ordered pair to the canonical Lehmann transition data. -/
noncomputable def eigenbasisTransitionData
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (mn : ι × ι) : LehmannTransitionData system.hbar :=
  orderedLehmannTransitionData system.hbar
    (data.energy mn.1) (data.energy mn.2)
    (data.probability mn.1) (data.probability mn.2)
    (inner ℂ (data.basis mn.1) (A (data.basis mn.2)))
    (inner ℂ (data.basis mn.2) (B (data.basis mn.1)))

@[simp]
theorem eigenbasisTransitionData_energyGap
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (mn : ι × ι) :
    (eigenbasisTransitionData system data A B mn).energyGap =
      orderedLehmannEnergyGap (data.energy mn.1) (data.energy mn.2) := rfl

/-- Diagonal eigenbasis transitions have zero physical weight. -/
@[simp]
theorem eigenbasisTransitionData_weight_diag
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (i : ι) :
    (eigenbasisTransitionData system data A B (i, i)).weight = 0 := by
  simp [eigenbasisTransitionData]

/-- Absolute-summability condition for the countable eigenbasis transition weights. -/
def EigenbasisLehmannSummable
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) : Prop :=
  Summable fun mn : ι × ι => ‖(eigenbasisTransitionData system data A B mn).weight‖

/-- The fixed-positive-rate eigenbasis Lehmann series. -/
noncomputable def eigenbasisLehmannSeries
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) : ℂ :=
  ∑' mn : ι × ι,
    (eigenbasisTransitionData system data A B mn).frequencyTerm omega eta

/-- Absolute transition-weight summability implies summability of the fixed-rate eigenbasis
Lehmann series for every `eta > 0`. -/
theorem summable_eigenbasisLehmannSeries_of_pos
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ)
    (hsum : EigenbasisLehmannSummable system data A B) (heta : 0 < eta) :
    Summable fun mn : ι × ι =>
      (eigenbasisTransitionData system data A B mn).frequencyTerm omega eta := by
  simpa [LehmannTransitionData.frequencyTerm] using
    LehmannTransitionData.summable_frequencyTerm_of_pos
      omega eta (eigenbasisTransitionData system data A B) hsum heta

/-- In finite dimension, the absolute transition-weight condition is automatic. -/
theorem eigenbasisLehmannSummable_of_finite
    [Finite ι] (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) :
    EigenbasisLehmannSummable system data A B := by
  exact Summable.of_finite

/-- For a finite spectral index, the countable-series definition reduces to the usual finite
double sum. -/
theorem eigenbasisLehmannSeries_eq_finite_sum
    [Fintype ι] (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) :
    eigenbasisLehmannSeries system data A B omega eta =
      ∑ mn : ι × ι,
        (eigenbasisTransitionData system data A B mn).frequencyTerm omega eta := by
  simp [eigenbasisLehmannSeries, LehmannTransitionData.frequencyTerm]

end
end LinearResponse
end QuantumTheory
