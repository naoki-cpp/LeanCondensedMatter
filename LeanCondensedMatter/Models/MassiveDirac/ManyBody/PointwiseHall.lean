import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.TwoModeResponse
import LeanCondensedMatter.Models.MassiveDirac.Bastin.Interband

set_option linter.style.header false

/-! # Pointwise full-Fock origin of the clean interband Hall density

At each physical momentum the two energy bands are two fermionic modes. Their four occupation
states supply the full-Fock Kubo response. A singly occupied band gives the corresponding band
contribution; filled-state responses are assembled by their occupation differences. This does
not construct a global infinite-volume density operator.
-/

namespace QuantumTheory.Models.MassiveDirac

open SecondQuantization.Fermionic.Transport
open ContinuousLinearMap
open scoped BigOperators

noncomputable section

private def modeBand (i : Fin 2) : Band := if i = 0 then .lower else .upper

private def bandMode : Band → Fin 2
  | .lower => 0
  | .upper => 1

private theorem pureProbability_nonneg (occupied n : Finset (Fin 2)) :
    0 ≤ (if n = occupied then (1 : ℝ) else 0) := by
  split_ifs <;> norm_num

private theorem pureProbability_hasSum (occupied : Finset (Fin 2)) :
    HasSum (fun n : Finset (Fin 2) => if n = occupied then (1 : ℝ) else 0) 1 := by
  classical
  have h : Summable (fun n : Finset (Fin 2) => if n = occupied then (1 : ℝ) else 0) :=
    Summable.of_finite
  simpa [tsum_fintype] using h.hasSum

private def pointwiseFockCurrentMatrix (direction : Fin 2) (e v m px py : ℝ)
    (hE : energy v m px py ≠ 0) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => inner ℂ ((pointwiseEigenbasisData v m px py hE).eigenbasis (modeBand i))
    (currentOperator direction e v
      ((pointwiseEigenbasisData v m px py hE).eigenbasis (modeBand j)))

/-- Antisymmetric four-state Fock Kubo response of a specified occupied-band configuration.
Time is scaled with `hbar = 1`; the physical static trace normalization is attached downstream. -/
def pointwiseFockHallResponse (occupied : Finset Band) (e v m px py eta : ℝ)
    (hE : energy v m px py ≠ 0) : ℂ :=
  let modes := Finset.univ.filter (fun i => modeBand i ∈ occupied)
  twoModeFockHallKuboResponse (fun i => bandEnergy (modeBand i) v m px py)
    (fun n => if n = modes then 1 else 0)
    (pointwiseFockCurrentMatrix 0 e v m px py hE)
    (pointwiseFockCurrentMatrix 1 e v m px py hE) 1 (by norm_num)
    (pureProbability_nonneg modes) (pureProbability_hasSum modes) eta

/-- Clean real Hall density of the singly occupied band, evaluated through the full-Fock
transition coefficient. At the Dirac degeneracy the totalized density is set to zero. -/
def cleanBandFockHallDensity (band : Band) (e v m px py : ℝ) : ℝ :=
  if hE : energy v m px py ≠ 0 then
    twoModeFockHallCleanResponse (fun i => bandEnergy (modeBand i) v m px py)
      (fun n => if n = {bandMode band} then 1 else 0)
      (pointwiseFockCurrentMatrix 0 e v m px py hE)
      (pointwiseFockCurrentMatrix 1 e v m px py hE) 1
  else 0

/-- The clean density is obtained by taking the switching-rate limit of the actual four-state
Fock response, rather than postulating a one-particle Berry weight. -/
theorem tendsto_pointwiseFockHallResponse_re
    (occupied : Finset Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Filter.Tendsto (fun eta => (pointwiseFockHallResponse occupied e v m px py eta hE).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ band ∈ occupied, cleanBandFockHallDensity band e v m px py)) := by
  classical
  let modes := Finset.univ.filter (fun i : Fin 2 => modeBand i ∈ occupied)
  have hgap : bandEnergy (modeBand 0) v m px py - bandEnergy (modeBand 1) v m px py ≠ 0 := by
    simpa [modeBand] using interbandEnergyGap_ne_zero_of_energy_ne_zero Band.lower v m px py hE
  have h := tendsto_twoModeFockHallKuboResponse_re
    (fun i => bandEnergy (modeBand i) v m px py)
    (fun n => if n = modes then 1 else 0)
    (pointwiseFockCurrentMatrix 0 e v m px py hE)
    (pointwiseFockCurrentMatrix 1 e v m px py hE) 1 (by norm_num)
    (pureProbability_nonneg modes) (pureProbability_hasSum modes) hgap
  have hstates : (Finset.univ : Finset (Finset Band)) =
      {∅, {.lower}, {.upper}, {.lower, .upper}} := by decide
  have hcases : occupied = ∅ ∨ occupied = {.lower} ∨ occupied = {.upper} ∨
      occupied = {.lower, .upper} := by
    have hmem := Finset.mem_univ occupied
    rw [hstates] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  have hmodes : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have hvalue : twoModeFockHallCleanResponse
      (fun i => bandEnergy (modeBand i) v m px py) (fun n => if n = modes then 1 else 0)
      (pointwiseFockCurrentMatrix 0 e v m px py hE)
      (pointwiseFockCurrentMatrix 1 e v m px py hE) 1 =
        ∑ band ∈ occupied, cleanBandFockHallDensity band e v m px py := by
    rcases hcases with rfl | rfl | rfl | rfl <;>
      simp [modes, hmodes, modeBand, bandMode, cleanBandFockHallDensity, hE,
        twoModeFockHallCleanResponse] <;> ring
  rw [hvalue] at h
  exact h

/-- The current-matrix coefficient extracted from the full-Fock Kubo limit equals the
canonical negative charge-squared Berry curvature for the occupied band. -/
theorem cleanBandFockHallDensity_eq_neg_chargeSq_berryCurvature
    (band : Band) (e v m px py : ℝ) :
    cleanBandFockHallDensity band e v m px py = -(e ^ 2 * berryCurvature band v m px py) := by
  by_cases hE : energy v m px py ≠ 0
  swap
  · simp [cleanBandFockHallDensity, hE, berryCurvature, not_ne_iff.mp hE]
  let data := pointwiseEigenbasisData v m px py hE
  have hblock (mu nu : Fin 2) (source target : Band) :
      currentBandBlockTrace mu nu source target e v m px py =
        inner ℂ (data.eigenbasis target) (currentOperator mu e v (data.eigenbasis source)) *
          inner ℂ (data.eigenbasis source) (currentOperator nu e v (data.eigenbasis target)) := by
    unfold currentBandBlockTrace
    rw [bandProjectorOperator_eq_rankOne_pointwiseEigenbasis target v m px py hE,
      bandProjectorOperator_eq_rankOne_pointwiseEigenbasis source v m px py hE]
    change _ = inner ℂ (data.eigenbasis target)
      (currentOperator mu e v (data.eigenbasis source)) *
        inner ℂ (data.eigenbasis source) (currentOperator nu e v (data.eigenbasis target))
    rw [show InnerProductSpace.rankOne ℂ (data.eigenbasis target) (data.eigenbasis target) *
        currentOperator mu e v *
        InnerProductSpace.rankOne ℂ (data.eigenbasis source) (data.eigenbasis source) *
        currentOperator nu e v =
      inner ℂ (data.eigenbasis target) (currentOperator mu e v (data.eigenbasis source)) •
        InnerProductSpace.rankOne ℂ (data.eigenbasis target)
          ((currentOperator nu e v).adjoint (data.eigenbasis source)) by
      simp [ContinuousLinearMap.mul_def, InnerProductSpace.comp_rankOne,
        InnerProductSpace.rankOne_comp, ContinuousLinearMap.adjoint_inner_left]]
    simp [finiteDimensionalOperatorTrace_apply, InnerProductSpace.trace_rankOne,
      ContinuousLinearMap.adjoint_inner_left]
  rw [← bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_chargeSq_berryCurvature
    band e v m px py hE]
  unfold cleanBandFockHallDensity
  rw [dif_pos hE]
  cases band <;>
    simp [twoModeFockHallCleanResponse, bandMode, modeBand, pointwiseFockCurrentMatrix,
      bastinInterbandBlockDifference, hblock, data, interbandEnergyGap, bandEnergy,
      currentBandBlockTrace_swap, mul_comm] <;> ring

end
end QuantumTheory.Models.MassiveDirac
