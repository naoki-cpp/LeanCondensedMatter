import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.LinearResponse.ConservationLaws
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option linter.style.header false

/-!
# Pure-point density states and free dynamics

This module supplies the state and dynamics bridge needed to identify the countable pure-point
Lehmann series with the retarded susceptibility.

A `PurePointLehmannData` probability distribution is first realized as the canonical diagonal
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
private theorem purePointProbability_summable_norm
    (data : PurePointLehmannData system ι) :
    Summable fun i => ‖data.probability i‖ := by
  have h : Summable fun i => |data.probability i| :=
    data.probability_summable.congr fun i => by
      rw [abs_of_nonneg (data.probability_nonneg i)]
  simpa only [Real.norm_eq_abs] using h

/-- File-local positivity proof required by the diagonal density constructor. -/
private theorem purePointProbability_tsum_pos
    (data : PurePointLehmannData system ι) :
    0 < ∑' i, data.probability i := by
  rw [data.probability_tsum]
  exact zero_lt_one

/-- The canonical density operator represented by the pure-point probabilities. -/
noncomputable def purePointDensityOperator
    (data : PurePointLehmannData system ι) : DensityOperator H :=
  diagonalDensityOperator data.basis data.probability
    (purePointProbability_summable_norm system data) data.probability_nonneg
    (purePointProbability_tsum_pos system data)

/-- The pure-point density operator acts diagonally with the original normalized probabilities. -/
@[simp]
theorem purePointDensityOperator_apply_basis
    (data : PurePointLehmannData system ι) (i : ι) :
    (purePointDensityOperator system data).op (data.basis i) =
      (data.probability i : ℂ) • data.basis i := by
  simpa [purePointDensityOperator, normalizedDiagonalWeight, data.probability_tsum] using
    diagonalDensityOperator_apply_basis data.basis data.probability
      (purePointProbability_summable_norm system data) data.probability_nonneg
      (purePointProbability_tsum_pos system data) i

/-- The pure-point density operator commutes with the Hamiltonian because both are diagonal in the
same Hilbert basis. -/
theorem commute_hamiltonian_purePointDensityOperator
    (data : PurePointLehmannData system ι) :
    Commute system.hamiltonian.1 (purePointDensityOperator system data).op := by
  change system.hamiltonian.1 * (purePointDensityOperator system data).op =
    (purePointDensityOperator system data).op * system.hamiltonian.1
  apply ContinuousLinearMap.ext
  intro x
  have hleft :=
    (data.basis.hasSum_repr x).mapL
      (system.hamiltonian.1 * (purePointDensityOperator system data).op)
  have hright :=
    (data.basis.hasSum_repr x).mapL
      ((purePointDensityOperator system data).op * system.hamiltonian.1)
  apply hleft.unique
  convert hright using 1
  funext i
  simp [mul_apply_eq_comp, data.hamiltonian_apply_basis, smul_smul, mul_comm]

/-- The normalized response expectation is the canonical expectation of the pure-point density
operator. -/
noncomputable def purePointNormalizedExpectation
    (data : PurePointLehmannData system ι) : NormalizedExpectation H :=
  (purePointDensityOperator system data).toNormalizedExpectation

@[simp]
theorem purePointNormalizedExpectation_apply
    (data : PurePointLehmannData system ι)
    (A : H →L[ℂ] H) :
    purePointNormalizedExpectation system data A =
      ∑' i, (data.probability i : ℂ) *
        inner ℂ (data.basis i) (A (data.basis i)) := by
  rw [purePointNormalizedExpectation, DensityOperator.toNormalizedExpectation_apply]
  exact (purePointDensityOperator system data).expectation_eq_tsum_diagonal
    A data.basis data.probability (purePointDensityOperator_apply_basis system data)

/-- The exponent of the free Schrödinger phase of one energy-basis vector. -/
noncomputable def purePointSchrodingerExponent
    (data : PurePointLehmannData system ι) (i : ι) (t : ℝ) : ℂ :=
  -(Complex.I * (((t * data.energy i) / system.hbar : ℝ) : ℂ))

/-- The scalar free Schrödinger phase of one energy-basis vector. -/
noncomputable def purePointSchrodingerPhase
    (data : PurePointLehmannData system ι) (i : ι) (t : ℝ) : ℂ :=
  Complex.exp (purePointSchrodingerExponent system data i t)

/-- The time-scaled Schrödinger generator acts diagonally on the energy basis. -/
theorem timeScaledGenerator_apply_purePointBasis
    (data : PurePointLehmannData system ι) (i : ι) (t : ℝ) :
    timeScaledGenerator system t (data.basis i) =
      purePointSchrodingerExponent system data i t • data.basis i := by
  rw [timeScaledGenerator, schrodingerGenerator]
  simp only [smul_apply, data.hamiltonian_apply_basis, smul_smul]
  congr 1
  rw [purePointSchrodingerExponent]
  push_cast
  ring

/-- Every power of the time-scaled generator remains diagonal on the energy basis. -/
theorem pow_timeScaledGenerator_apply_purePointBasis
    (data : PurePointLehmannData system ι) (i : ι) (t : ℝ) (n : ℕ) :
    ((timeScaledGenerator system t) ^ n) (data.basis i) =
      (purePointSchrodingerExponent system data i t) ^ n • data.basis i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simp only [mul_apply_eq_comp,
        timeScaledGenerator_apply_purePointBasis, map_smul, ih, smul_smul]
      congr 1
      ring

/-- The free propagator acts on an energy-basis vector by the expected Schrödinger phase. -/
theorem freePropagator_apply_purePointBasis
    (data : PurePointLehmannData system ι) (i : ι) (t : ℝ) :
    freePropagator system t (data.basis i) =
      purePointSchrodingerPhase system data i t • data.basis i := by
  let T : H →L[ℂ] H := timeScaledGenerator system t
  let c : ℂ := purePointSchrodingerExponent system data i t
  let v : H := data.basis i
  have hop :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T).mapL
      (ContinuousLinearMap.apply ℂ H v)
  have hop' : HasSum
      (fun n : ℕ => (((n.factorial : ℂ)⁻¹ * c ^ n) • v))
      (freePropagator system t v) := by
    convert hop using 1
    · ext n
      simp only [ContinuousLinearMap.apply_apply, smul_apply]
      rw [pow_timeScaledGenerator_apply_purePointBasis]
      simp [c, v, smul_smul]
    · rfl
  have hscalar :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).mapL
      (ContinuousLinearMap.toSpanSingleton ℂ v)
  have hscalar' : HasSum
      (fun n : ℕ => (((n.factorial : ℂ)⁻¹ * c ^ n) • v))
      (purePointSchrodingerPhase system data i t • v) := by
    convert hscalar using 1
    · ext n
      simp
    · simp [purePointSchrodingerPhase, Complex.exp_eq_exp_ℂ, c, v]
  exact hop'.unique hscalar'

/-- The relative phase carried by a Heisenberg-picture matrix element. -/
noncomputable def purePointTransitionPhase
    (data : PurePointLehmannData system ι)
    (m n : ι) (t : ℝ) : ℂ :=
  star (purePointSchrodingerPhase system data m t) *
    purePointSchrodingerPhase system data n t

/-- The relative Schrödinger phases combine into the usual energy-difference phase. -/
theorem purePointTransitionPhase_eq_exp_energyDifference
    (data : PurePointLehmannData system ι)
    (m n : ι) (t : ℝ) :
    purePointTransitionPhase system data m n t =
      Complex.exp
        (Complex.I * ((((data.energy m - data.energy n) * t) /
          system.hbar : ℝ) : ℂ)) := by
  rw [purePointTransitionPhase, purePointSchrodingerPhase,
    purePointSchrodingerPhase, Complex.exp_eq_exp_ℂ]
  rw [NormedSpace.star_exp, ← NormedSpace.exp_add]
  congr 1
  simp [purePointSchrodingerExponent]
  ring

/-- Matrix elements of a freely evolved observable acquire the energy-difference phase. -/
theorem inner_purePointBasis_heisenbergEvolution
    (data : PurePointLehmannData system ι)
    (A : H →L[ℂ] H) (m n : ι) (t : ℝ) :
    inner ℂ (data.basis m)
        (heisenbergEvolution system A t (data.basis n)) =
      purePointTransitionPhase system data m n t *
        inner ℂ (data.basis m) (A (data.basis n)) := by
  rw [heisenbergEvolution]
  simp only [mul_apply_eq_comp]
  rw [freePropagator_apply_purePointBasis system data n t]
  rw [map_smul]
  rw [← star_freePropagator system t]
  rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [freePropagator_apply_purePointBasis system data m t]
  simp [purePointTransitionPhase, inner_smul_left, inner_smul_right]
  ring

/-- The canonical pure-point density expectation is stationary under the free dynamics. -/
theorem isStationary_purePointNormalizedExpectation
    (data : PurePointLehmannData system ι) :
    IsStationary system (purePointNormalizedExpectation system data) := by
  simpa [purePointNormalizedExpectation] using
    isStationary_toNormalizedExpectation_of_commute_hamiltonian system
      (purePointDensityOperator system data)
      (commute_hamiltonian_purePointDensityOperator system data)

end
end LinearResponse
end QuantumTheory
