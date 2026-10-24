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
from the general conservation law. It also proves the free energy-basis phases used downstream.

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

/-- The scalar free Schrödinger phase of one energy-basis vector. -/
noncomputable def eigenbasisSchrodingerPhase
    (data : EnergyEigenbasisLehmannData system ι) (i : ι) (t : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (((t * data.energy i) / system.hbar : ℝ) : ℂ)))

/-- The free propagator acts on an energy-basis vector by the expected Schrödinger phase. -/
theorem freePropagator_apply_energyEigenbasis
    (data : EnergyEigenbasisLehmannData system ι) (i : ι) (t : ℝ) :
    freePropagator system t (data.basis i) =
      eigenbasisSchrodingerPhase system data i t • data.basis i := by
  let T : H →L[ℂ] H := (t : ℂ) • schrodingerGenerator system
  let c : ℂ := -(Complex.I * (((t * data.energy i) / system.hbar : ℝ) : ℂ))
  let v : H := data.basis i
  have hT : T v = c • v := by
    dsimp [T, c, v]
    rw [schrodingerGenerator]
    simp only [smul_apply, data.hamiltonian_apply_basis, smul_smul]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) t
      ((-(Complex.I / (system.hbar : ℂ)) * (data.energy i : ℂ)) • data.basis i)]
    rw [smul_smul]
    apply congrArg (fun z : ℂ => z • data.basis i)
    push_cast
    simp only [div_eq_mul_inv, neg_mul, mul_neg]
    apply congrArg (fun z : ℂ => -z)
    simp [mul_assoc, mul_left_comm, mul_comm]
  have hpow (n : ℕ) : (T ^ n) v = c ^ n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        simp only [mul_apply_eq_comp, ih, map_smul, hT, smul_smul]
        congr 1
        ring
  have hop :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T).mapL
      (ContinuousLinearMap.apply ℂ H v)
  have hop' : HasSum
      (fun n : ℕ => (((n.factorial : ℂ)⁻¹ * c ^ n) • v))
      (freePropagator system t v) := by
    convert hop using 1
    · ext n
      simp only [ContinuousLinearMap.apply_apply, smul_apply]
      rw [hpow]
      simp [c, v, smul_smul]
    · rfl
  have hscalar :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).mapL
      (ContinuousLinearMap.toSpanSingleton ℂ v)
  have hscalar' : HasSum
      (fun n : ℕ => (((n.factorial : ℂ)⁻¹ * c ^ n) • v))
      (eigenbasisSchrodingerPhase system data i t • v) := by
    convert hscalar using 1
    · ext n
      simp
    · simp [eigenbasisSchrodingerPhase, Complex.exp_eq_exp_ℂ, c, v]
  exact hop'.unique hscalar'

/-- The relative phase carried by a Heisenberg-picture matrix element. -/
noncomputable def eigenbasisTransitionPhase
    (data : EnergyEigenbasisLehmannData system ι)
    (m n : ι) (t : ℝ) : ℂ :=
  star (eigenbasisSchrodingerPhase system data m t) *
    eigenbasisSchrodingerPhase system data n t

/-- The relative Schrödinger phases combine into the usual energy-difference phase. -/
theorem eigenbasisTransitionPhase_eq_exp_energyDifference
    (data : EnergyEigenbasisLehmannData system ι)
    (m n : ι) (t : ℝ) :
    eigenbasisTransitionPhase system data m n t =
      Complex.exp
        (Complex.I * (((orderedLehmannEnergyGap (data.energy m) (data.energy n) * t) /
          system.hbar : ℝ) : ℂ)) := by
  rw [eigenbasisTransitionPhase, eigenbasisSchrodingerPhase,
    eigenbasisSchrodingerPhase, Complex.exp_eq_exp_ℂ]
  rw [NormedSpace.star_exp, ← NormedSpace.exp_add]
  congr 1
  simp
  ring

/-- Matrix elements of a freely evolved observable acquire the energy-difference phase. -/
theorem inner_energyEigenbasis_heisenbergEvolution
    (data : EnergyEigenbasisLehmannData system ι)
    (A : H →L[ℂ] H) (m n : ι) (t : ℝ) :
    inner ℂ (data.basis m)
        (heisenbergEvolution (freePropagatorGroup system) t A (data.basis n)) =
      eigenbasisTransitionPhase system data m n t *
        inner ℂ (data.basis m) (A (data.basis n)) := by
  rw [heisenbergEvolution_freePropagatorGroup_apply]
  simp only [mul_apply_eq_comp]
  rw [freePropagator_apply_energyEigenbasis system data n t]
  rw [map_smul]
  rw [← star_freePropagator system t]
  rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [freePropagator_apply_energyEigenbasis system data m t]
  simp [eigenbasisTransitionPhase, inner_smul_left, inner_smul_right]
  ring

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
