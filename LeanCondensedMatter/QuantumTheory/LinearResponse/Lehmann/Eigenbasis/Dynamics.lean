import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Eigenstate
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.ConservationLaws
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Eigenbasis.Data
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option linter.style.header false

/-!
# Eigenbasis density states and free dynamics

This module supplies the state and dynamics bridge needed to identify the countable eigenbasis
Lehmann series with the retarded susceptibility.

A `EnergyEigenbasisLehmannData` probability distribution is first realized as the canonical diagonal
`DensityOperator`. Its normalized expectation is then obtained through
`DensityOperator.toNormalizedExpectation`; no parallel linear-functional construction is retained.
The module proves that this density state commutes with the Hamiltonian and derives stationarity
from the general conservation law. It supplies the energy-difference phase used downstream.

The countable double-sum expansion of the commutator and the exchange of that sum with the time
integral are intentionally left to the next layer.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

open scoped InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}
variable (system : BoundedFreeSystem H)

/-- File-local absolute summability proof required by the diagonal density constructor. -/
private theorem eigenbasisProbability_summable_norm
    (data : EnergyEigenbasisLehmannData system ι) :
    Summable fun i => ‖data.probability i‖ :=
  data.probability_hasSum.summable.norm

/-- File-local positivity proof required by the diagonal density constructor. -/
private theorem eigenbasisProbability_tsum_pos
    (data : EnergyEigenbasisLehmannData system ι) :
    0 < ∑' i, data.probability i := by
  simpa [data.probability_hasSum.tsum_eq]

/-- The canonical density operator represented by the eigenbasis probabilities. -/
noncomputable def eigenbasisDensityOperator
    (data : EnergyEigenbasisLehmannData system ι) : DensityOperator H :=
  diagonalDensityOperator data.basis data.probability
    (eigenbasisProbability_summable_norm system data) data.probability_nonneg
    (eigenbasisProbability_tsum_pos system data)

/-- The eigenbasis density operator acts diagonally with the original normalized probabilities. -/
@[simp]
theorem eigenbasisDensityOperator_apply_basis
    (data : EnergyEigenbasisLehmannData system ι) (i : ι) :
    (eigenbasisDensityOperator system data).op (data.basis i) =
      (data.probability i : ℂ) • data.basis i := by
  simpa [eigenbasisDensityOperator, Real.normalizedWeight,
    data.probability_hasSum.tsum_eq] using
    diagonalDensityOperator_apply_basis data.basis data.probability
      (eigenbasisProbability_summable_norm system data) data.probability_nonneg
      (eigenbasisProbability_tsum_pos system data) i

/-- The eigenbasis density operator commutes with the Hamiltonian because both are diagonal in the
same Hilbert basis. -/
theorem commute_hamiltonian_eigenbasisDensityOperator
    (data : EnergyEigenbasisLehmannData system ι) :
    Commute system.hamiltonian.1 (eigenbasisDensityOperator system data).op := by
  change system.hamiltonian.1 * (eigenbasisDensityOperator system data).op =
    (eigenbasisDensityOperator system data).op * system.hamiltonian.1
  apply ContinuousLinearMap.ext
  intro x
  have hleft :=
    (data.basis.hasSum_repr x).mapL
      (system.hamiltonian.1 * (eigenbasisDensityOperator system data).op)
  have hright :=
    (data.basis.hasSum_repr x).mapL
      ((eigenbasisDensityOperator system data).op * system.hamiltonian.1)
  apply hleft.unique
  convert hright using 1
  funext i
  simp [mul_apply_eq_comp, data.hamiltonian_apply_basis, smul_smul, mul_comm]

/-- The normalized response expectation is the canonical expectation of the eigenbasis density
operator. -/
noncomputable def eigenbasisNormalizedExpectation
    (data : EnergyEigenbasisLehmannData system ι) : NormalizedExpectation H :=
  (eigenbasisDensityOperator system data).toNormalizedExpectation

@[simp]
theorem eigenbasisNormalizedExpectation_apply
    (data : EnergyEigenbasisLehmannData system ι)
    (A : H →L[ℂ] H) :
    eigenbasisNormalizedExpectation system data A =
      ∑' i, (data.probability i : ℂ) *
        inner ℂ (data.basis i) (A (data.basis i)) := by
  rw [eigenbasisNormalizedExpectation, DensityOperator.toNormalizedExpectation_apply]
  exact (eigenbasisDensityOperator system data).expectation_eq_tsum_diagonal
    A data.basis data.probability (eigenbasisDensityOperator_apply_basis system data)

/-- Probability one at a single basis state already forces all other weights
to vanish. The canonical diagonal expectation is the pure vector expectation. -/
theorem eigenbasisNormalizedExpectation_eq_pure_of_single
    (data : EnergyEigenbasisLehmannData system ι) (occupied : ι)
    (hoccupied : data.probability occupied = 1) :
    eigenbasisNormalizedExpectation system data =
      (pure ⟨data.basis occupied, data.basis.orthonormal.1 occupied⟩).toNormalizedExpectation := by
  classical
  have hzero (i : ι) (hi : i ≠ occupied) : data.probability i = 0 := by
    have hle := data.probability_hasSum.summable.sum_le_tsum
      ({i, occupied} : Finset ι) (fun j _ => data.probability_nonneg j)
    rw [data.probability_hasSum.tsum_eq] at hle
    simp [hi, hoccupied] at hle
    exact le_antisymm hle (data.probability_nonneg i)
  have hext (p q : NormalizedExpectation H)
      (h : p.toContinuousLinearMap = q.toContinuousLinearMap) : p = q := by
    cases p
    cases q
    cases h
    rfl
  apply hext
  apply ContinuousLinearMap.ext
  intro A
  let ψ : StateVector H := ⟨data.basis occupied, data.basis.orthonormal.1 occupied⟩
  change eigenbasisNormalizedExpectation system data A = (pure ψ).toNormalizedExpectation A
  calc
    eigenbasisNormalizedExpectation system data A =
        inner ℂ (data.basis occupied) (A (data.basis occupied)) := by
      rw [eigenbasisNormalizedExpectation_apply, tsum_eq_single occupied]
      · simp [hoccupied]
      · intro i hi
        simp [hzero i hi]
    _ = (pure ψ).toNormalizedExpectation A := by
      change inner ℂ ψ.1 (A ψ.1) = (pure ψ).expectation A
      exact (DensityOperator.expectation_pure ψ A).symm

/-- The relative phase carried by a Heisenberg-picture matrix element. -/
noncomputable def eigenbasisTransitionPhase
    (data : EnergyEigenbasisLehmannData system ι)
    (m n : ι) (t : ℝ) : ℂ :=
  Complex.exp
    (Complex.I * (((orderedLehmannEnergyGap (data.energy m) (data.energy n) * t) /
      system.hbar : ℝ) : ℂ))

/-- The canonical eigenbasis density expectation is stationary under the free dynamics. -/
theorem isStationary_eigenbasisNormalizedExpectation
    (data : EnergyEigenbasisLehmannData system ι) :
    IsStationary (freePropagatorGroup system) (eigenbasisNormalizedExpectation system data) := by
  simpa [eigenbasisNormalizedExpectation] using
    isStationary_toNormalizedExpectation_of_commute_hamiltonian system
      (eigenbasisDensityOperator system data)
      (commute_hamiltonian_eigenbasisDensityOperator system data)

end
end LinearResponse
end QuantumTheory
