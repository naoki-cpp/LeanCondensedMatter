import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.TwoModeResponse
import LeanCondensedMatter.Models.MassiveDirac.Bastin.Interband
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-! # Pointwise full-Fock origin of the clean interband Hall density

At each physical momentum the two energy bands are two fermionic modes. Their four occupation
states supply the full-Fock Kubo response. Normalized diagonal states contribute through their
mean band occupations. Pure filled configurations and grand-canonical Gibbs probabilities use
this same response; the latter yield Fermi--Dirac occupations. This does not construct a global
infinite-volume density operator or interchange the pointwise limit with momentum integration.
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

private def pointwiseFockCurrentMatrix (direction : Fin 2) (e v m px py : ℝ)
    (hE : energy v m px py ≠ 0) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => inner ℂ ((pointwiseEigenbasisData v m px py hE).eigenbasis (modeBand i))
    (currentOperator direction e v
      ((pointwiseEigenbasisData v m px py hE).eigenbasis (modeBand j)))

/-- Antisymmetric four-state Fock Kubo response in a normalized occupation-diagonal state.
Mode `0` is the lower band and mode `1` is the upper band. Physical time evolution uses
the band energies and the supplied reduced Planck constant, independently of the state. -/
def pointwiseDiagonalFockHallResponse (probability : Finset (Fin 2) → ℝ)
    (hpos : ∀ n, 0 ≤ probability n) (hsum : HasSum probability 1) (e v m px py hbar : ℝ)
    (hhbar : 0 < hbar) (eta : ℝ)
    (hE : energy v m px py ≠ 0) : ℂ :=
  twoModeFockHallKuboResponse (fun i => bandEnergy (modeBand i) v m px py)
    probability
    (pointwiseFockCurrentMatrix 0 e v m px py hE)
    (pointwiseFockCurrentMatrix 1 e v m px py hE) hbar hhbar
    hpos hsum eta

/-- Response of one occupied-band configuration, including the vacuum and double occupation. -/
def pointwiseFockHallResponse (occupied : Finset Band) (e v m px py hbar : ℝ)
    (hhbar : 0 < hbar) (eta : ℝ) (hE : energy v m px py ≠ 0) : ℂ :=
  let modes := Finset.univ.filter (fun i => modeBand i ∈ occupied)
  pointwiseDiagonalFockHallResponse (fun n => if n = modes then 1 else 0)
    (by intro n; by_cases h : n = modes <;> simp [h])
    (by
      classical
      have h : Summable (fun n : Finset (Fin 2) => if n = modes then (1 : ℝ) else 0) :=
        Summable.of_finite
      simpa [tsum_fintype] using h.hasSum)
    e v m px py hbar hhbar eta hE

/-- Grand-canonical four-state response at inverse temperature `beta` and chemical potential
`mu`. The Gibbs generator determines the state, while physical band energies generate time. -/
def pointwiseGrandCanonicalFockHallResponse (beta mu e v m px py hbar : ℝ)
    (hhbar : 0 < hbar) (eta : ℝ) (hE : energy v m px py ≠ 0) : ℂ :=
  let E := SecondQuantization.Common.grandCanonicalEnergy (Config := Finset (Fin 2))
    (fun i => bandEnergy (modeBand i) v m px py) mu
  pointwiseDiagonalFockHallResponse (eigenbasisGibbsProbability E beta)
    (eigenbasisGibbsProbability_nonneg E beta)
    (hasSum_eigenbasisGibbsProbability E beta (eigenbasisGibbsSummable_of_finite E beta))
    e v m px py hbar hhbar eta hE

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

/-- The clean response of any normalized diagonal state is weighted by its mean band
occupations. Double occupation contributes to both marginals, and cancels in their difference. -/
theorem tendsto_pointwiseDiagonalFockHallResponse_re
    (probability : Finset (Fin 2) → ℝ) (hpos : ∀ n, 0 ≤ probability n)
    (hsum : HasSum probability 1) (e v m px py hbar : ℝ) (hhbar : 0 < hbar)
    (hE : energy v m px py ≠ 0) :
    Filter.Tendsto (fun eta =>
      (pointwiseDiagonalFockHallResponse probability hpos hsum e v m px py hbar hhbar eta hE).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (hbar * ∑ band : Band,
        (probability {if band = .lower then 0 else 1} + probability {0, 1}) *
          cleanBandFockHallDensity band e v m px py)) := by
  classical
  have hgap : bandEnergy (modeBand 0) v m px py - bandEnergy (modeBand 1) v m px py ≠ 0 := by
    simpa [modeBand, interbandEnergyGap, bandEnergy] using
      interbandEnergyGap_ne_zero_of_energy_ne_zero Band.lower v m px py hE
  have h := tendsto_twoModeFockHallKuboResponse_re
    (fun i => bandEnergy (modeBand i) v m px py)
    probability
    (pointwiseFockCurrentMatrix 0 e v m px py hE)
    (pointwiseFockCurrentMatrix 1 e v m px py hE) hbar hhbar
    hpos hsum hgap
  have hvalue : twoModeFockHallCleanResponse
      (fun i => bandEnergy (modeBand i) v m px py) probability
      (pointwiseFockCurrentMatrix 0 e v m px py hE)
      (pointwiseFockCurrentMatrix 1 e v m px py hE) hbar =
        hbar * ∑ band : Band,
          (probability {if band = .lower then 0 else 1} + probability {0, 1}) *
            cleanBandFockHallDensity band e v m px py := by
    simp [sum_band, modeBand, bandMode, cleanBandFockHallDensity, hE,
      twoModeFockHallCleanResponse]
    ring
  rw [hvalue] at h
  exact h

/-- The normalized many-body Gibbs response yields Fermi--Dirac band occupations, without
normalizing them as one-particle probabilities. No global infinite-volume Gibbs state is used. -/
theorem tendsto_pointwiseGrandCanonicalFockHallResponse_re
    (beta mu e v m px py hbar : ℝ) (hhbar : 0 < hbar) (hE : energy v m px py ≠ 0) :
    Filter.Tendsto (fun eta =>
      (pointwiseGrandCanonicalFockHallResponse beta mu e v m px py hbar hhbar eta hE).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (hbar * ∑ band : Band,
        (Real.exp (beta * (bandEnergy band v m px py - mu)) + 1)⁻¹ *
          cleanBandFockHallDensity band e v m px py)) := by
  classical
  let eps : Fin 2 → ℝ := fun i => bandEnergy (modeBand i) v m px py
  let E := SecondQuantization.Common.grandCanonicalEnergy (Config := Finset (Fin 2)) eps mu
  let p := eigenbasisGibbsProbability E beta
  have henergy : E = SecondQuantization.Fermionic.fermionEnergy (fun i => eps i - mu) := by
    funext n
    exact SecondQuantization.Common.grandCanonicalEnergy_eq_shifted eps mu n
  have hZ : eigenbasisPartitionFunction E beta =
      (1 + Real.exp (-beta * (eps 0 - mu))) *
        (1 + Real.exp (-beta * (eps 1 - mu))) := by
    apply Complex.ofReal_injective
    have h := SecondQuantization.Fermionic.coe_grandCanonicalPartitionFunction_eq_prod eps beta mu
    simpa [SecondQuantization.Common.grandCanonicalPartitionFunction, E,
      Fin.prod_univ_two, Complex.ofReal_exp] using h
  have hocc (i : Fin 2) : p {i} + p {0, 1} =
      (Real.exp (beta * (eps i - mu)) + 1)⁻¹ := by
    have hf : (Real.exp (beta * (eps i - mu)) + 1)⁻¹ =
        Real.exp (-beta * (eps i - mu)) / (1 + Real.exp (-beta * (eps i - mu))) := by
      rw [show -beta * (eps i - mu) = -(beta * (eps i - mu)) by ring, Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    rw [hf]
    have h0 := ne_of_gt (add_pos zero_lt_one (Real.exp_pos (-beta * (eps 0 - mu))))
    have h1 := ne_of_gt (add_pos zero_lt_one (Real.exp_pos (-beta * (eps 1 - mu))))
    simp only [p, eigenbasisGibbsProbability]
    simp only [hZ]
    simp only [eigenbasisBoltzmannWeight, henergy,
      SecondQuantization.Fermionic.fermionEnergy_eq_sum,
      Finset.sum_insert (by decide : (0 : Fin 2) ∉ {1}), Finset.sum_singleton,
      mul_add, Real.exp_add]
    fin_cases i
    all_goals field_simp [h0, h1]
    all_goals ring
  have h := tendsto_pointwiseDiagonalFockHallResponse_re p
    (eigenbasisGibbsProbability_nonneg E beta)
    (hasSum_eigenbasisGibbsProbability E beta (eigenbasisGibbsSummable_of_finite E beta))
    e v m px py hbar hhbar hE
  simp_rw [hocc] at h
  simpa [eps, modeBand, sum_band, pointwiseGrandCanonicalFockHallResponse, p, E] using h

/-- A filled configuration is a special case of the normalized diagonal-state response. -/
theorem tendsto_pointwiseFockHallResponse_re
    (occupied : Finset Band) (e v m px py hbar : ℝ) (hhbar : 0 < hbar)
    (hE : energy v m px py ≠ 0) :
    Filter.Tendsto (fun eta => (pointwiseFockHallResponse occupied e v m px py hbar hhbar eta hE).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (hbar * ∑ band ∈ occupied, cleanBandFockHallDensity band e v m px py)) := by
  classical
  let modes := Finset.univ.filter (fun i : Fin 2 => modeBand i ∈ occupied)
  let p : Finset (Fin 2) → ℝ := fun n => if n = modes then 1 else 0
  have hpos : ∀ n, 0 ≤ p n := by intro n; by_cases hn : n = modes <;> simp [p, hn]
  have hsum : HasSum p 1 := by
    have hp : Summable p := Summable.of_finite
    simpa [p, tsum_fintype] using hp.hasSum
  have h := tendsto_pointwiseDiagonalFockHallResponse_re p hpos hsum e v m px py hbar hhbar hE
  have hvalue : (∑ band : Band,
      (p {if band = .lower then 0 else 1} + p {0, 1}) *
        cleanBandFockHallDensity band e v m px py) =
      ∑ band ∈ occupied, cleanBandFockHallDensity band e v m px py := by
    have hstates : (Finset.univ : Finset (Finset Band)) =
        {∅, {.lower}, {.upper}, {.lower, .upper}} := by decide
    have hmem := Finset.mem_univ occupied
    rw [hstates] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hmodes : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    have hn0 : ({0, 1} : Finset (Fin 2)) ≠ {0} := by decide
    have hn1 : ({0, 1} : Finset (Fin 2)) ≠ {1} := by decide
    rcases hmem with rfl | rfl | rfl | rfl <;>
      simp [sum_band, p, modes, hmodes, modeBand, Finset.filter_insert,
        Finset.filter_singleton, hn0, hn1, Ne.symm hn0, Ne.symm hn1]
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
