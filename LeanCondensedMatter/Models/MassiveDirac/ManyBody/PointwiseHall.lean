import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.TwoModeResponse
import LeanCondensedMatter.Models.MassiveDirac.Bastin.Interband
import Mathlib.Tactic.Ring

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
  by_cases h : n = occupied <;> simp [h]

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

/-- Antisymmetric four-state Fock Kubo response of a specified occupied-band configuration,
with the physical reduced Planck constant supplied to the time evolution. -/
def pointwiseFockHallResponse (occupied : Finset Band) (e v m px py hbar : ℝ)
    (hhbar : 0 < hbar) (eta : ℝ)
    (hE : energy v m px py ≠ 0) : ℂ :=
  let modes := Finset.univ.filter (fun i => modeBand i ∈ occupied)
  twoModeFockHallKuboResponse (fun i => bandEnergy (modeBand i) v m px py)
    (fun n => if n = modes then 1 else 0)
    (pointwiseFockCurrentMatrix 0 e v m px py hE)
    (pointwiseFockCurrentMatrix 1 e v m px py hE) hbar hhbar
    (pureProbability_nonneg modes) (pureProbability_hasSum modes) eta

/-- Clean Hall coefficient per unit reduced Planck constant for a singly occupied band,
evaluated through the full-Fock transition coefficient. At the Dirac degeneracy the totalized
density is set to zero. The physical response limit carries an explicit factor `hbar`. -/
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
    (occupied : Finset Band) (e v m px py hbar : ℝ) (hhbar : 0 < hbar)
    (hE : energy v m px py ≠ 0) :
    Filter.Tendsto (fun eta => (pointwiseFockHallResponse occupied e v m px py hbar hhbar eta hE).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (hbar * ∑ band ∈ occupied, cleanBandFockHallDensity band e v m px py)) := by
  classical
  let modes := Finset.univ.filter (fun i : Fin 2 => modeBand i ∈ occupied)
  have hgap : bandEnergy (modeBand 0) v m px py - bandEnergy (modeBand 1) v m px py ≠ 0 := by
    simpa [modeBand, interbandEnergyGap, bandEnergy] using
      interbandEnergyGap_ne_zero_of_energy_ne_zero Band.lower v m px py hE
  have h := tendsto_twoModeFockHallKuboResponse_re
    (fun i => bandEnergy (modeBand i) v m px py)
    (fun n => if n = modes then 1 else 0)
    (pointwiseFockCurrentMatrix 0 e v m px py hE)
    (pointwiseFockCurrentMatrix 1 e v m px py hE) hbar hhbar
    (pureProbability_nonneg modes) (pureProbability_hasSum modes) hgap
  have hstates : (Finset.univ : Finset (Finset Band)) =
      {∅, {.lower}, {.upper}, {.lower, .upper}} := by decide
  have hcases : occupied = ∅ ∨ occupied = {.lower} ∨ occupied = {.upper} ∨
      occupied = {.lower, .upper} := by
    have hmem := Finset.mem_univ occupied
    rw [hstates] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  have hmodes : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have hf0 : ({0, 1} : Finset (Fin 2)).filter (fun i => i = 0) = {0} := by decide
  have hf1 : ({0, 1} : Finset (Fin 2)).filter (fun i => i ≠ 0) = {1} := by decide
  have hfall : ({0, 1} : Finset (Fin 2)).filter (fun i => i = 0 ∨ i ≠ 0) = {0, 1} := by decide
  have hn0 : ({0} : Finset (Fin 2)) ≠ {0, 1} := by decide
  have hn1 : ({1} : Finset (Fin 2)) ≠ {0, 1} := by decide
  have hvalue : twoModeFockHallCleanResponse
      (fun i => bandEnergy (modeBand i) v m px py) (fun n => if n = modes then 1 else 0)
      (pointwiseFockCurrentMatrix 0 e v m px py hE)
      (pointwiseFockCurrentMatrix 1 e v m px py hE) hbar =
        hbar * ∑ band ∈ occupied, cleanBandFockHallDensity band e v m px py := by
    rcases hcases with rfl | rfl | rfl | rfl <;>
      (simp [modes, hmodes, modeBand, bandMode, cleanBandFockHallDensity, hE,
        twoModeFockHallCleanResponse, hf0, hf1, hfall, hn0, hn1])
    all_goals ring_nf
    all_goals simp
  rw [hvalue] at h
  exact h

/-- The current-matrix coefficient extracted from the full-Fock Kubo limit equals the
canonical negative charge-squared Berry curvature for the occupied band. -/
theorem cleanBandFockHallDensity_eq_neg_chargeSq_berryCurvature
    (band : Band) (e v m px py : ℝ) :
    cleanBandFockHallDensity band e v m px py = -(e ^ 2 * berryCurvature band v m px py) := by
  by_cases hE : energy v m px py ≠ 0
  swap
  · simp [cleanBandFockHallDensity, berryCurvature, not_ne_iff.mp hE]
  let data := pointwiseEigenbasisData v m px py hE
  have hblock (mu nu : Fin 2) (source target : Band) :
      currentBandBlockTrace mu nu source target e v m px py =
        inner ℂ (data.eigenbasis target) (currentOperator mu e v (data.eigenbasis source)) *
          inner ℂ (data.eigenbasis source) (currentOperator nu e v (data.eigenbasis target)) := by
    unfold currentBandBlockTrace
    rw [bandProjectorOperator_eq_rankOne_pointwiseEigenbasis target v m px py hE,
      bandProjectorOperator_eq_rankOne_pointwiseEigenbasis source v m px py hE]
    generalize currentOperator mu e v = J₁
    generalize currentOperator nu e v = J₂
    rw [show InnerProductSpace.rankOne ℂ (data.eigenbasis target) (data.eigenbasis target) *
        J₁ *
        InnerProductSpace.rankOne ℂ (data.eigenbasis source) (data.eigenbasis source) *
        J₂ =
      inner ℂ (data.eigenbasis target) (J₁ (data.eigenbasis source)) •
        InnerProductSpace.rankOne ℂ (data.eigenbasis target)
          (J₂.adjoint (data.eigenbasis source)) by
      simp [ContinuousLinearMap.mul_def, InnerProductSpace.comp_rankOne,
        InnerProductSpace.rankOne_comp, ContinuousLinearMap.adjoint_inner_left]]
    simp [finiteDimensionalOperatorTrace_apply, InnerProductSpace.trace_rankOne,
      ContinuousLinearMap.adjoint_inner_left]
  have hmat (mu nu : Fin 2) (i j : Fin 2) :
      pointwiseFockCurrentMatrix mu e v m px py hE i j *
        pointwiseFockCurrentMatrix nu e v m px py hE j i =
      currentBandBlockTrace mu nu (modeBand j) (modeBand i) e v m px py := by
    simpa only [pointwiseFockCurrentMatrix, data] using
      (hblock mu nu (modeBand j) (modeBand i)).symm
  rw [← bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_chargeSq_berryCurvature
    band e v m px py hE]
  unfold cleanBandFockHallDensity
  rw [dite_eq_left hE]
  cases band <;>
    (simp [twoModeFockHallCleanResponse, bandMode, modeBand,
      bastinInterbandBlockDifference, hmat, interbandEnergyGap, bandEnergy,
      currentBandBlockTrace_swap])
  all_goals ring

end
end QuantumTheory.Models.MassiveDirac
