import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option linter.style.header false

/-!
# Pure-point expectations and free dynamics

This module supplies the state and dynamics bridge needed to identify the countable pure-point
Lehmann series with the previously defined retarded susceptibility.

From `PurePointLehmannData` it constructs the normalized diagonal expectation

`ω(A) = ∑' i, pᵢ ⟪i, A i⟫`,

proves that the free propagator acts on every energy-basis vector by its Schrödinger phase, derives
the corresponding Heisenberg-picture matrix-element phase, and proves stationarity of the diagonal
expectation.

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

/-- One diagonal pure-point expectation term. -/
noncomputable def purePointExpectationTerm
    (data : PurePointLehmannData system ι)
    (A : H →L[ℂ] H) (i : ι) : ℂ :=
  (data.probability i : ℂ) *
    inner ℂ (data.basis i) (A (data.basis i))

/-- The diagonal expectation series is summable for every bounded observable. -/
theorem summable_purePointExpectationTerm
    (data : PurePointLehmannData system ι)
    (A : H →L[ℂ] H) :
    Summable (purePointExpectationTerm system data A) := by
  have hp : Summable fun i => |data.probability i| :=
    data.probability_summable.congr fun i => by
      rw [abs_of_nonneg (data.probability_nonneg i)]
  refine Summable.of_norm_bounded (hp.mul_right ‖A‖) fun i => ?_
  have hinner :
      ‖inner ℂ (data.basis i) (A (data.basis i))‖ ≤ ‖A‖ := by
    calc
      ‖inner ℂ (data.basis i) (A (data.basis i))‖ ≤
          ‖data.basis i‖ * ‖A (data.basis i)‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖data.basis i‖ * (‖A‖ * ‖data.basis i‖) := by
        gcongr
        exact A.le_opNorm _
      _ = ‖A‖ := by
        rw [data.basis.orthonormal.1 i]
        ring
  rw [purePointExpectationTerm, norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left hinner (abs_nonneg _)

/-- The unbundled diagonal expectation value. -/
noncomputable def purePointExpectationValue
    (data : PurePointLehmannData system ι)
    (A : H →L[ℂ] H) : ℂ :=
  ∑' i, purePointExpectationTerm system data A i

private theorem purePointExpectationValue_add
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) :
    purePointExpectationValue system data (A + B) =
      purePointExpectationValue system data A +
        purePointExpectationValue system data B := by
  rw [purePointExpectationValue, purePointExpectationValue, purePointExpectationValue,
    ← ((summable_purePointExpectationTerm system data A).hasSum.add
      (summable_purePointExpectationTerm system data B).hasSum).tsum_eq]
  apply tsum_congr
  intro i
  simp [purePointExpectationTerm, inner_add_right, mul_add]

private theorem purePointExpectationValue_smul
    (data : PurePointLehmannData system ι)
    (c : ℂ) (A : H →L[ℂ] H) :
    purePointExpectationValue system data (c • A) =
      c * purePointExpectationValue system data A := by
  rw [purePointExpectationValue, purePointExpectationValue,
    ← ((summable_purePointExpectationTerm system data A).hasSum.mul_left c).tsum_eq]
  apply tsum_congr
  intro i
  simp [purePointExpectationTerm, inner_smul_right]
  ring

private theorem purePointExpectationValue_norm_le
    (data : PurePointLehmannData system ι)
    (A : H →L[ℂ] H) :
    ‖purePointExpectationValue system data A‖ ≤ ‖A‖ := by
  rw [purePointExpectationValue]
  have hp : HasSum (fun i => |data.probability i|) 1 := by
    have hprob : HasSum data.probability 1 := by
      rw [← data.probability_tsum]
      exact data.probability_summable.hasSum
    have hfun : (fun i => |data.probability i|) = data.probability := by
      funext i
      rw [abs_of_nonneg (data.probability_nonneg i)]
    simpa only [hfun] using hprob
  have hbound : HasSum (fun i => |data.probability i| * ‖A‖) (1 * ‖A‖) :=
    hp.mul_right ‖A‖
  have hle :
      ‖∑' i, purePointExpectationTerm system data A i‖ ≤ 1 * ‖A‖ := by
    apply tsum_of_norm_bounded hbound
    intro i
    have hinner :
        ‖inner ℂ (data.basis i) (A (data.basis i))‖ ≤ ‖A‖ := by
      calc
        ‖inner ℂ (data.basis i) (A (data.basis i))‖ ≤
            ‖data.basis i‖ * ‖A (data.basis i)‖ :=
          norm_inner_le_norm _ _
        _ ≤ ‖data.basis i‖ * (‖A‖ * ‖data.basis i‖) := by
          gcongr
          exact A.le_opNorm _
        _ = ‖A‖ := by
          rw [data.basis.orthonormal.1 i]
          ring
    rw [purePointExpectationTerm, norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
  simpa using hle

/-- The normalized expectation associated with the pure-point probabilities. -/
noncomputable def purePointNormalizedExpectation
    (data : PurePointLehmannData system ι) : NormalizedExpectation H where
  toContinuousLinearMap :=
    IsBoundedLinearMap.toContinuousLinearMap
      (fun A : H →L[ℂ] H => purePointExpectationValue system data A)
      { map_add := purePointExpectationValue_add system data
        map_smul := fun c A => by
          simpa only [smul_eq_mul] using
            purePointExpectationValue_smul system data c A
        bound := ⟨1, zero_lt_one, fun A => by
          simpa using purePointExpectationValue_norm_le system data A⟩ }
  map_one := by
    change purePointExpectationValue system data 1 = 1
    rw [purePointExpectationValue]
    calc
      (∑' i, purePointExpectationTerm system data 1 i) =
          ∑' i, (data.probability i : ℂ) := by
        apply tsum_congr
        intro i
        simp [purePointExpectationTerm, inner_self_eq_norm_sq_to_K,
          data.basis.orthonormal.1 i]
      _ = 1 := by
        exact_mod_cast data.probability_tsum

@[simp]
theorem purePointNormalizedExpectation_apply
    (data : PurePointLehmannData system ι)
    (A : H →L[ℂ] H) :
    purePointNormalizedExpectation system data A =
      ∑' i, (data.probability i : ℂ) *
        inner ℂ (data.basis i) (A (data.basis i)) :=
  rfl

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

/-- The diagonal pure-point expectation is stationary under the free dynamics. -/
theorem isStationary_purePointNormalizedExpectation
    (data : PurePointLehmannData system ι) :
    IsStationary system (purePointNormalizedExpectation system data) := by
  intro t A
  simp only [purePointNormalizedExpectation_apply]
  apply tsum_congr
  intro i
  rw [inner_purePointBasis_heisenbergEvolution system data A i i t]
  rw [purePointTransitionPhase_eq_exp_energyDifference]
  simp

end
end LinearResponse
end QuantumTheory
