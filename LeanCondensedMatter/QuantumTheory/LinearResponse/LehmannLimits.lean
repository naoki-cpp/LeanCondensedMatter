import LeanCondensedMatter.QuantumTheory.LinearResponse.LimitOrder

set_option linter.style.header false

/-!
# Nonresonant limits of finite Lehmann sums

This module gives concrete existence theorems for the limit-order API.  The inner limits are required
only locally near the point used by the outer limit, because a finite spectrum can have resonant
frequencies away from `omega = 0`.

If every zero-energy-gap transition has zero spectral weight, then both `omega → 0` followed by
`eta → 0⁺` and `eta → 0⁺` followed by `omega → 0` exist locally and converge to the same
unswitched static finite Lehmann sum.  Finite families are represented by
`κ → LehmannTransitionData hbar`, so the gap, weight, and reduced Planck constant stay on one
canonical transition seam.
-/

namespace QuantumTheory
namespace LinearResponse

open Set Filter Topology

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

/-- One zero-rate scalar Lehmann term. -/
noncomputable def unswitchedLehmannTerm
    (hbar omega energyGap : ℝ) (weight : ℂ) : ℂ :=
  lehmannTerm hbar omega 0 energyGap weight

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
      (unswitchedLehmannTerm hbar omega energyGap weight) := by
  rcases hregular with hweight | hdetuning
  · subst weight
    simp [HasAdiabaticRemovalLimit, unswitchedLehmannTerm, lehmannTerm]
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
theorem hasStaticLimit_unswitchedLehmannTerm
    (hbar energyGap : ℝ) (weight : ℂ) (hhbar : hbar ≠ 0)
    (hregular : weight = 0 ∨ energyGap ≠ 0) :
    HasStaticLimit
      (fun omega : ℝ => unswitchedLehmannTerm hbar omega energyGap weight)
      (unswitchedLehmannTerm hbar 0 energyGap weight) := by
  rcases hregular with hweight | hgap
  · subst weight
    simp [HasStaticLimit, unswitchedLehmannTerm, lehmannTerm]
  · have hgapDiv : energyGap / hbar ≠ 0 :=
      div_ne_zero hgap hhbar
    have hdetuning : (0 : ℝ) + energyGap / hbar ≠ 0 := by
      simpa only [zero_add] using hgapDiv
    have hden : ContinuousAt
        (fun omega : ℝ => lehmannDenominator hbar omega 0 energyGap) 0 := by
      unfold lehmannDenominator
      fun_prop
    have hcont : ContinuousAt
        (fun omega : ℝ => unswitchedLehmannTerm hbar omega energyGap weight) 0 := by
      unfold unswitchedLehmannTerm lehmannTerm
      exact continuousAt_const.mul
        (hden.inv₀ (lehmannDenominator_zero_rate_ne_zero
          hbar 0 energyGap hdetuning))
    simpa [HasStaticLimit] using hcont.tendsto

namespace LehmannTransitionData

/-- Zero-rate contribution of one canonical transition. -/
noncomputable def unswitchedTerm
    {hbar : ℝ} (transition : LehmannTransitionData hbar) (omega : ℝ) : ℂ :=
  unswitchedLehmannTerm hbar omega transition.energyGap transition.weight

end LehmannTransitionData

/-- Fixed-nonzero-rate finite Lehmann sums always have a static limit. -/
private theorem hasStaticLimit_finiteLehmannLimitSum
    {κ : Type*} (s : Finset κ)
    (hbar eta : ℝ) (transition : κ → LehmannTransitionData hbar)
    (heta : eta ≠ 0) :
    HasStaticLimit
      (fun omega : ℝ =>
        s.sum fun j => (transition j).frequencyTerm omega eta)
      (s.sum fun j => (transition j).frequencyTerm 0 eta) := by
  unfold LehmannTransitionData.frequencyTerm
  apply HasStaticLimit.finsetSum
  intro j _
  exact hasStaticLimit_lehmannTerm
    hbar eta (transition j).energyGap (transition j).weight heta

/-- Regulator removal for a finite sum whose nonzero-weight terms are nonresonant. -/
private theorem hasAdiabaticRemovalLimit_finiteLehmannLimitSum
    {κ : Type*} (s : Finset κ)
    (hbar omega : ℝ) (transition : κ → LehmannTransitionData hbar)
    (hregular : ∀ j ∈ s,
      (transition j).weight = 0 ∨ omega + (transition j).energyGap / hbar ≠ 0) :
    HasAdiabaticRemovalLimit
      (fun eta : ℝ =>
        s.sum fun j => (transition j).frequencyTerm omega eta)
      (s.sum fun j => (transition j).unswitchedTerm omega) := by
  unfold LehmannTransitionData.frequencyTerm LehmannTransitionData.unswitchedTerm
  apply HasAdiabaticRemovalLimit.finsetSum
  intro j hj
  exact hasAdiabaticRemovalLimit_lehmannTerm
    hbar omega (transition j).energyGap (transition j).weight (hregular j hj)

/-- Static continuity of a finite zero-rate nonresonant sum. -/
private theorem hasStaticLimit_finiteUnswitchedLehmannSum
    {κ : Type*} (s : Finset κ)
    (hbar : ℝ) (transition : κ → LehmannTransitionData hbar)
    (hhbar : hbar ≠ 0)
    (hregular : ∀ j ∈ s,
      (transition j).weight = 0 ∨ (transition j).energyGap ≠ 0) :
    HasStaticLimit
      (fun omega : ℝ =>
        s.sum fun j => (transition j).unswitchedTerm omega)
      (s.sum fun j => (transition j).unswitchedTerm 0) := by
  unfold LehmannTransitionData.unswitchedTerm
  apply HasStaticLimit.finsetSum
  intro j hj
  exact hasStaticLimit_unswitchedLehmannTerm
    hbar (transition j).energyGap (transition j).weight hhbar (hregular j hj)

/-- Near zero frequency, every finite static-nonresonant sum admits regulator removal. -/
private theorem eventually_hasAdiabaticRemovalLimit_finiteLehmannLimitSum
    {κ : Type*} (s : Finset κ)
    (hbar : ℝ) (transition : κ → LehmannTransitionData hbar)
    (hhbar : hbar ≠ 0)
    (hregular : ∀ j ∈ s,
      (transition j).weight = 0 ∨ (transition j).energyGap ≠ 0) :
    ∀ᶠ omega : ℝ in 𝓝 0,
      HasAdiabaticRemovalLimit
        (fun eta : ℝ =>
          s.sum fun j => (transition j).frequencyTerm omega eta)
        (s.sum fun j => (transition j).unswitchedTerm omega) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact Filter.Eventually.of_forall fun _ => by
        simp [HasAdiabaticRemovalLimit]
  | @insert a s ha ih =>
      have haRegular := hregular a (Finset.mem_insert_self a s)
      have hsRegular : ∀ j ∈ s,
          (transition j).weight = 0 ∨ (transition j).energyGap ≠ 0 := by
        intro j hj
        exact hregular j (Finset.mem_insert_of_mem hj)
      have hterm : ∀ᶠ omega : ℝ in 𝓝 0,
          HasAdiabaticRemovalLimit
            (fun eta : ℝ =>
              (transition a).frequencyTerm omega eta)
            ((transition a).unswitchedTerm omega) := by
        rcases haRegular with hweight | hgap
        · exact Filter.Eventually.of_forall fun omega => by
            simpa [LehmannTransitionData.frequencyTerm,
              LehmannTransitionData.unswitchedTerm] using
              hasAdiabaticRemovalLimit_lehmannTerm
                hbar omega (transition a).energyGap (transition a).weight
                  (Or.inl hweight)
        · have hgapDiv : (transition a).energyGap / hbar ≠ 0 :=
            div_ne_zero hgap hhbar
          have hvalue : (0 : ℝ) + (transition a).energyGap / hbar ≠ 0 := by
            simpa only [zero_add] using hgapDiv
          have hcont : ContinuousAt
              (fun omega : ℝ => omega + (transition a).energyGap / hbar) 0 := by
            fun_prop
          filter_upwards [hcont.eventually_ne hvalue] with omega hdetuning
          simpa [LehmannTransitionData.frequencyTerm,
            LehmannTransitionData.unswitchedTerm] using
            hasAdiabaticRemovalLimit_lehmannTerm
              hbar omega (transition a).energyGap (transition a).weight
                (Or.inr hdetuning)
      filter_upwards [hterm, ih hsRegular] with omega htermOmega hsOmega
      unfold HasAdiabaticRemovalLimit at htermOmega hsOmega ⊢
      simpa [Finset.sum_insert, ha] using htermOmega.add hsOmega

/-- Both local iterated limits exist and agree for a finite static-nonresonant family. -/
private theorem finiteLehmannLimitSum_has_both_local_iterated_limits
    {κ : Type*} (s : Finset κ)
    (hbar : ℝ) (transition : κ → LehmannTransitionData hbar)
    (hhbar : hbar ≠ 0)
    (hregular : ∀ j ∈ s,
      (transition j).weight = 0 ∨ (transition j).energyGap ≠ 0) :
    HasLocalStaticThenAdiabaticLimit
        (fun omega eta =>
          s.sum fun j => (transition j).frequencyTerm omega eta)
        (s.sum fun j => (transition j).unswitchedTerm 0) ∧
      HasLocalAdiabaticThenStaticLimit
        (fun omega eta =>
          s.sum fun j => (transition j).frequencyTerm omega eta)
        (s.sum fun j => (transition j).unswitchedTerm 0) := by
  constructor
  · refine ⟨fun eta =>
      s.sum fun j => (transition j).frequencyTerm 0 eta, ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin] with eta heta
      exact hasStaticLimit_finiteLehmannLimitSum
        s hbar eta transition (ne_of_gt heta)
    · apply hasAdiabaticRemovalLimit_finiteLehmannLimitSum
      intro j hj
      rcases hregular j hj with hweight | hgap
      · exact Or.inl hweight
      · have hgapDiv : (transition j).energyGap / hbar ≠ 0 :=
          div_ne_zero hgap hhbar
        exact Or.inr (by simpa only [zero_add] using hgapDiv)
  · refine ⟨fun omega =>
      s.sum fun j => (transition j).unswitchedTerm omega, ?_, ?_⟩
    · exact eventually_hasAdiabaticRemovalLimit_finiteLehmannLimitSum
        s hbar transition hhbar hregular
    · exact hasStaticLimit_finiteUnswitchedLehmannSum
        s hbar transition hhbar hregular

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]
variable (system : BoundedFreeSystem H)

/-- Static nonresonance for a finite pure-point response. Degenerate transitions are allowed when
their physical transition weight vanishes. -/
def PurePointStaticNonresonant
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) : Prop :=
  ∀ mn : ι × ι,
    (purePointTransitionData system data A B mn).weight = 0 ∨
      (purePointTransitionData system data A B mn).energyGap ≠ 0

/-- A finite static-nonresonant pure-point Lehmann formula has both local iterated limits, with the
same zero-rate static double sum. -/
theorem finite_purePointLehmann_has_both_local_iterated_limits
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H)
    (hregular : PurePointStaticNonresonant system data A B) :
    HasLocalStaticThenAdiabaticLimit
        (fun omega eta =>
          Finset.univ.sum fun mn : ι × ι =>
            lehmannTerm system.hbar omega eta
              (data.energy mn.1 - data.energy mn.2)
              (purePointTransitionWeight system data A B mn))
        (Finset.univ.sum fun mn : ι × ι =>
          unswitchedLehmannTerm system.hbar 0
            (data.energy mn.1 - data.energy mn.2)
            (purePointTransitionWeight system data A B mn)) ∧
      HasLocalAdiabaticThenStaticLimit
        (fun omega eta =>
          Finset.univ.sum fun mn : ι × ι =>
            lehmannTerm system.hbar omega eta
              (data.energy mn.1 - data.energy mn.2)
              (purePointTransitionWeight system data A B mn))
        (Finset.univ.sum fun mn : ι × ι =>
          unswitchedLehmannTerm system.hbar 0
            (data.energy mn.1 - data.energy mn.2)
            (purePointTransitionWeight system data A B mn)) := by
  simpa [LehmannTransitionData.frequencyTerm, LehmannTransitionData.unswitchedTerm,
    purePointTransitionWeight] using
    finiteLehmannLimitSum_has_both_local_iterated_limits
      (s := Finset.univ)
      system.hbar
      (purePointTransitionData system data A B)
      (ne_of_gt system.hbar_pos)
      (fun mn _ => hregular mn)

end
end LinearResponse
end QuantumTheory
