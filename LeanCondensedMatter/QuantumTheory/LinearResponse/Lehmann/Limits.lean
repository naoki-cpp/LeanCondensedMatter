import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.LimitOrder
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Transition

set_option linter.style.header false

/-! # Limits of scalar Lehmann transition families -/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory Filter Topology

noncomputable section

/-- At zero switching rate, nonzero detuning makes the scalar denominator nonzero. -/
theorem lehmannDenominator_zero_rate_ne_zero
    (hbar omega energyGap : ℝ)
    (hdetuning : omega + energyGap / hbar ≠ 0) :
    lehmannDenominator hbar omega 0 energyGap ≠ 0 := by
  intro hzero
  have him : -(omega + energyGap / hbar) = 0 := by
    simpa [lehmannDenominator] using congrArg Complex.im hzero
  exact hdetuning (neg_eq_zero.mp him)

/-- At fixed nonzero rate, a scalar Lehmann term has the direct static limit. -/
theorem hasStaticLimit_lehmannTerm
    (hbar eta energyGap : ℝ) (weight : ℂ) (heta : eta ≠ 0) :
    HasStaticLimit
      (fun omega : ℝ => lehmannTerm hbar omega eta energyGap weight)
      (lehmannTerm hbar 0 eta energyGap weight) := by
  have hden : ContinuousAt
      (fun omega : ℝ => lehmannDenominator hbar omega eta energyGap) 0 := by
    unfold lehmannDenominator
    fun_prop
  have hcont : ContinuousAt
      (fun omega : ℝ => lehmannTerm hbar omega eta energyGap weight) 0 := by
    unfold lehmannTerm
    exact continuousAt_const.mul
      (hden.inv₀ (lehmannDenominator_ne_zero
        hbar 0 eta energyGap heta))
  simpa [HasStaticLimit] using hcont.tendsto

/-- Regulator removal for one scalar term, provided its weight vanishes or it is nonresonant. -/
theorem hasAdiabaticRemovalLimit_lehmannTerm
    (hbar omega energyGap : ℝ) (weight : ℂ)
    (hregular : weight = 0 ∨ omega + energyGap / hbar ≠ 0) :
    HasAdiabaticRemovalLimit
      (fun eta : ℝ => lehmannTerm hbar omega eta energyGap weight)
      (lehmannTerm hbar omega 0 energyGap weight) := by
  rcases hregular with hweight | hdetuning
  · subst weight
    simp [HasAdiabaticRemovalLimit, lehmannTerm]
  · have hden : ContinuousAt
        (fun eta : ℝ => lehmannDenominator hbar omega eta energyGap) 0 := by
      unfold lehmannDenominator
      fun_prop
    have hcont : ContinuousAt
        (fun eta : ℝ => lehmannTerm hbar omega eta energyGap weight) 0 := by
      unfold lehmannTerm
      exact continuousAt_const.mul
        (hden.inv₀ (lehmannDenominator_zero_rate_ne_zero
          hbar omega energyGap hdetuning))
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- Static continuity of one zero-rate term under zero weight or nonzero energy gap. -/
theorem hasStaticLimit_lehmannTerm_zero_rate
    (hbar energyGap : ℝ) (weight : ℂ) (hhbar : hbar ≠ 0)
    (hregular : weight = 0 ∨ energyGap ≠ 0) :
    HasStaticLimit
      (fun omega : ℝ => lehmannTerm hbar omega 0 energyGap weight)
      (lehmannTerm hbar 0 0 energyGap weight) := by
  rcases hregular with hweight | hgap
  · subst weight
    simp [HasStaticLimit, lehmannTerm]
  · have hgapDiv : energyGap / hbar ≠ 0 :=
      div_ne_zero hgap hhbar
    have hdetuning : (0 : ℝ) + energyGap / hbar ≠ 0 := by
      simpa only [zero_add] using hgapDiv
    have hden : ContinuousAt
        (fun omega : ℝ => lehmannDenominator hbar omega 0 energyGap) 0 := by
      unfold lehmannDenominator
      fun_prop
    have hcont : ContinuousAt
        (fun omega : ℝ => lehmannTerm hbar omega 0 energyGap weight) 0 := by
      unfold lehmannTerm
      exact continuousAt_const.mul
        (hden.inv₀ (lehmannDenominator_zero_rate_ne_zero
          hbar 0 energyGap hdetuning))
    simpa [HasStaticLimit] using hcont.tendsto

/-- Near zero frequency, every finite static-nonresonant sum admits regulator removal. -/
private theorem eventually_hasAdiabaticRemovalLimit_finset_frequencyTerm
    {κ : Type*} (s : Finset κ)
    (hbar : ℝ) (transition : κ → LehmannTransitionData hbar)
    (hhbar : hbar ≠ 0)
    (hregular : ∀ j ∈ s,
      (transition j).weight = 0 ∨ (transition j).energyGap ≠ 0) :
    ∀ᶠ omega : ℝ in 𝓝 0,
      HasAdiabaticRemovalLimit
        (fun eta : ℝ =>
          s.sum fun j => (transition j).frequencyTerm omega eta)
        (s.sum fun j => (transition j).frequencyTerm omega 0) := by
  have hterm : ∀ j ∈ s, ∀ᶠ omega : ℝ in 𝓝 0,
      HasAdiabaticRemovalLimit
        (fun eta : ℝ => (transition j).frequencyTerm omega eta)
        ((transition j).frequencyTerm omega 0) := by
    intro j hj
    rcases hregular j hj with hweight | hgap
    · exact Filter.Eventually.of_forall fun omega => by
        simpa [LehmannTransitionData.frequencyTerm] using
          hasAdiabaticRemovalLimit_lehmannTerm
            hbar omega (transition j).energyGap (transition j).weight
              (Or.inl hweight)
    · have hgapDiv : (transition j).energyGap / hbar ≠ 0 :=
        div_ne_zero hgap hhbar
      have hvalue : (0 : ℝ) + (transition j).energyGap / hbar ≠ 0 := by
        simpa only [zero_add] using hgapDiv
      have hcont : ContinuousAt
          (fun omega : ℝ => omega + (transition j).energyGap / hbar) 0 := by
        fun_prop
      filter_upwards [hcont.eventually_ne hvalue] with omega hdetuning
      simpa [LehmannTransitionData.frequencyTerm] using
        hasAdiabaticRemovalLimit_lehmannTerm
          hbar omega (transition j).energyGap (transition j).weight
            (Or.inr hdetuning)
  filter_upwards [(Filter.eventually_all_finset s).2 hterm] with omega h
  exact tendsto_finsetSum s h

/-- Both local iterated limits exist and agree for a finite static-nonresonant family. -/
theorem finset_frequencyTerm_has_both_local_iterated_limits
    {κ : Type*} (s : Finset κ)
    (hbar : ℝ) (transition : κ → LehmannTransitionData hbar)
    (hhbar : hbar ≠ 0)
    (hregular : ∀ j ∈ s,
      (transition j).weight = 0 ∨ (transition j).energyGap ≠ 0) :
    HasLocalStaticThenAdiabaticLimit
        (fun omega eta =>
          s.sum fun j => (transition j).frequencyTerm omega eta)
        (s.sum fun j => (transition j).frequencyTerm 0 0) ∧
      HasLocalAdiabaticThenStaticLimit
        (fun omega eta =>
          s.sum fun j => (transition j).frequencyTerm omega eta)
        (s.sum fun j => (transition j).frequencyTerm 0 0) := by
  constructor
  · refine ⟨fun eta =>
      s.sum fun j => (transition j).frequencyTerm 0 eta, ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin] with eta heta
      unfold LehmannTransitionData.frequencyTerm
      apply tendsto_finsetSum
      intro j _
      exact hasStaticLimit_lehmannTerm
        hbar eta (transition j).energyGap (transition j).weight (ne_of_gt heta)
    · unfold LehmannTransitionData.frequencyTerm
      apply tendsto_finsetSum
      intro j hj
      apply hasAdiabaticRemovalLimit_lehmannTerm
      rcases hregular j hj with hweight | hgap
      · exact Or.inl hweight
      · have hgapDiv : (transition j).energyGap / hbar ≠ 0 :=
          div_ne_zero hgap hhbar
        exact Or.inr (by simpa only [zero_add] using hgapDiv)
  · refine ⟨fun omega =>
      s.sum fun j => (transition j).frequencyTerm omega 0, ?_, ?_⟩
    · exact eventually_hasAdiabaticRemovalLimit_finset_frequencyTerm
        s hbar transition hhbar hregular
    · unfold LehmannTransitionData.frequencyTerm
      apply tendsto_finsetSum
      intro j hj
      exact hasStaticLimit_lehmannTerm_zero_rate
        hbar (transition j).energyGap (transition j).weight hhbar (hregular j hj)

end
end LinearResponse
end QuantumTheory
