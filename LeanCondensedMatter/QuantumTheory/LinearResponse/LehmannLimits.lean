import LeanCondensedMatter.QuantumTheory.LinearResponse.LimitOrder

set_option linter.style.header false

/-!
# Nonresonant limits of finite Lehmann sums

This module gives concrete existence theorems for the limit-order API.  The inner limits are required
only locally near the point used by the outer limit, because a finite spectrum can have resonant
frequencies away from `omega = 0`.

If every zero-energy-gap transition has zero spectral weight, then both `omega → 0` followed by
`eta → 0⁺` and `eta → 0⁺` followed by `omega → 0` exist locally and converge to the same
unswitched static finite Lehmann sum.
-/

namespace QuantumTheory
namespace LinearResponse

open Set Filter Topology

noncomputable section

/-- Local static-then-adiabatic order. -/
def HasLocalStaticThenAdiabaticLimit
    (F : ℝ → ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ staticAtRate : ℝ → ℂ,
    (∀ᶠ eta in nhdsWithin 0 (Ioi 0),
      HasStaticLimit (fun omega => F omega eta) (staticAtRate eta)) ∧
    HasAdiabaticRemovalLimit staticAtRate L

/-- Local adiabatic-then-static order. -/
def HasLocalAdiabaticThenStaticLimit
    (F : ℝ → ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ regulatorRemoved : ℝ → ℂ,
    (∀ᶠ omega in 𝓝 0,
      HasAdiabaticRemovalLimit (fun eta => F omega eta) (regulatorRemoved omega)) ∧
    HasStaticLimit regulatorRemoved L

/-- A positive switching rate makes every scalar Lehmann denominator nonzero. -/
theorem lehmannDenominator_ne_zero_of_pos
    (hbar omega eta energyGap : ℝ) (heta : 0 < eta) :
    lehmannDenominator hbar omega eta energyGap ≠ 0 := by
  intro hzero
  have hre : eta = 0 := by
    simpa [lehmannDenominator] using congrArg Complex.re hzero
  exact (ne_of_gt heta) hre

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

/-- At fixed positive rate, a scalar Lehmann term has the direct static limit. -/
theorem hasStaticLimit_lehmannTerm_of_pos
    (hbar eta energyGap : ℝ) (weight : ℂ) (heta : 0 < eta) :
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
      (hden.inv₀ (lehmannDenominator_ne_zero_of_pos
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

/-- A finite family of fixed-rate Lehmann terms. -/
noncomputable def finiteLehmannLimitSum
    {κ : Type*} (s : Finset κ)
    (hbar omega eta : ℝ) (energyGap : κ → ℝ) (weight : κ → ℂ) : ℂ :=
  s.sum fun j => lehmannTerm hbar omega eta (energyGap j) (weight j)

/-- The corresponding finite zero-rate sum. -/
noncomputable def finiteUnswitchedLehmannSum
    {κ : Type*} (s : Finset κ)
    (hbar omega : ℝ) (energyGap : κ → ℝ) (weight : κ → ℂ) : ℂ :=
  s.sum fun j => unswitchedLehmannTerm hbar omega (energyGap j) (weight j)

/-- Fixed-positive-rate finite Lehmann sums always have a static limit. -/
theorem hasStaticLimit_finiteLehmannLimitSum_of_pos
    {κ : Type*} (s : Finset κ)
    (hbar eta : ℝ) (energyGap : κ → ℝ) (weight : κ → ℂ)
    (heta : 0 < eta) :
    HasStaticLimit
      (fun omega : ℝ =>
        finiteLehmannLimitSum s hbar omega eta energyGap weight)
      (finiteLehmannLimitSum s hbar 0 eta energyGap weight) := by
  unfold finiteLehmannLimitSum
  apply HasStaticLimit.finsetSum
  intro j _
  exact hasStaticLimit_lehmannTerm_of_pos
    hbar eta (energyGap j) (weight j) heta

/-- Regulator removal for a finite sum whose nonzero-weight terms are nonresonant. -/
theorem hasAdiabaticRemovalLimit_finiteLehmannLimitSum
    {κ : Type*} (s : Finset κ)
    (hbar omega : ℝ) (energyGap : κ → ℝ) (weight : κ → ℂ)
    (hregular : ∀ j ∈ s,
      weight j = 0 ∨ omega + energyGap j / hbar ≠ 0) :
    HasAdiabaticRemovalLimit
      (fun eta : ℝ =>
        finiteLehmannLimitSum s hbar omega eta energyGap weight)
      (finiteUnswitchedLehmannSum s hbar omega energyGap weight) := by
  unfold finiteLehmannLimitSum finiteUnswitchedLehmannSum
  apply HasAdiabaticRemovalLimit.finsetSum
  intro j hj
  exact hasAdiabaticRemovalLimit_lehmannTerm
    hbar omega (energyGap j) (weight j) (hregular j hj)

/-- Static continuity of a finite zero-rate nonresonant sum. -/
theorem hasStaticLimit_finiteUnswitchedLehmannSum
    {κ : Type*} (s : Finset κ)
    (hbar : ℝ) (energyGap : κ → ℝ) (weight : κ → ℂ)
    (hhbar : hbar ≠ 0)
    (hregular : ∀ j ∈ s, weight j = 0 ∨ energyGap j ≠ 0) :
    HasStaticLimit
      (fun omega : ℝ =>
        finiteUnswitchedLehmannSum s hbar omega energyGap weight)
      (finiteUnswitchedLehmannSum s hbar 0 energyGap weight) := by
  unfold finiteUnswitchedLehmannSum
  apply HasStaticLimit.finsetSum
  intro j hj
  exact hasStaticLimit_unswitchedLehmannTerm
    hbar (energyGap j) (weight j) hhbar (hregular j hj)

/-- Near zero frequency, every finite static-nonresonant sum admits regulator removal. -/
theorem eventually_hasAdiabaticRemovalLimit_finiteLehmannLimitSum
    {κ : Type*} (s : Finset κ)
    (hbar : ℝ) (energyGap : κ → ℝ) (weight : κ → ℂ)
    (hhbar : hbar ≠ 0)
    (hregular : ∀ j ∈ s, weight j = 0 ∨ energyGap j ≠ 0) :
    ∀ᶠ omega : ℝ in 𝓝 0,
      HasAdiabaticRemovalLimit
        (fun eta : ℝ =>
          finiteLehmannLimitSum s hbar omega eta energyGap weight)
        (finiteUnswitchedLehmannSum s hbar omega energyGap weight) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact Filter.Eventually.of_forall fun _ => by
        simp [finiteLehmannLimitSum, finiteUnswitchedLehmannSum,
          HasAdiabaticRemovalLimit]
  | @insert a s ha ih =>
      have haRegular := hregular a (Finset.mem_insert_self a s)
      have hsRegular : ∀ j ∈ s, weight j = 0 ∨ energyGap j ≠ 0 := by
        intro j hj
        exact hregular j (Finset.mem_insert_of_mem hj)
      have hterm : ∀ᶠ omega : ℝ in 𝓝 0,
          HasAdiabaticRemovalLimit
            (fun eta : ℝ =>
              lehmannTerm hbar omega eta (energyGap a) (weight a))
            (unswitchedLehmannTerm hbar omega (energyGap a) (weight a)) := by
        rcases haRegular with hweight | hgap
        · exact Filter.Eventually.of_forall fun omega =>
            hasAdiabaticRemovalLimit_lehmannTerm
              hbar omega (energyGap a) (weight a) (Or.inl hweight)
        · have hgapDiv : energyGap a / hbar ≠ 0 :=
            div_ne_zero hgap hhbar
          have hvalue : (0 : ℝ) + energyGap a / hbar ≠ 0 := by
            simpa only [zero_add] using hgapDiv
          have hcont : ContinuousAt
              (fun omega : ℝ => omega + energyGap a / hbar) 0 := by
            fun_prop
          filter_upwards [hcont.eventually_ne hvalue] with omega hdetuning
          exact hasAdiabaticRemovalLimit_lehmannTerm
            hbar omega (energyGap a) (weight a) (Or.inr hdetuning)
      filter_upwards [hterm, ih hsRegular] with omega htermOmega hsOmega
      unfold HasAdiabaticRemovalLimit at htermOmega hsOmega ⊢
      simpa [finiteLehmannLimitSum, finiteUnswitchedLehmannSum,
        Finset.sum_insert, ha] using htermOmega.add hsOmega

/-- Both local iterated limits exist and agree for a finite static-nonresonant family. -/
theorem finiteLehmannLimitSum_has_both_local_iterated_limits
    {κ : Type*} (s : Finset κ)
    (hbar : ℝ) (energyGap : κ → ℝ) (weight : κ → ℂ)
    (hhbar : hbar ≠ 0)
    (hregular : ∀ j ∈ s, weight j = 0 ∨ energyGap j ≠ 0) :
    HasLocalStaticThenAdiabaticLimit
        (fun omega eta =>
          finiteLehmannLimitSum s hbar omega eta energyGap weight)
        (finiteUnswitchedLehmannSum s hbar 0 energyGap weight) ∧
      HasLocalAdiabaticThenStaticLimit
        (fun omega eta =>
          finiteLehmannLimitSum s hbar omega eta energyGap weight)
        (finiteUnswitchedLehmannSum s hbar 0 energyGap weight) := by
  constructor
  · refine ⟨fun eta =>
      finiteLehmannLimitSum s hbar 0 eta energyGap weight, ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin] with eta heta
      exact hasStaticLimit_finiteLehmannLimitSum_of_pos
        s hbar eta energyGap weight heta
    · apply hasAdiabaticRemovalLimit_finiteLehmannLimitSum
      intro j hj
      rcases hregular j hj with hweight | hgap
      · exact Or.inl hweight
      · have hgapDiv : energyGap j / hbar ≠ 0 :=
          div_ne_zero hgap hhbar
        exact Or.inr (by simpa only [zero_add] using hgapDiv)
  · refine ⟨fun omega =>
      finiteUnswitchedLehmannSum s hbar omega energyGap weight, ?_, ?_⟩
    · exact eventually_hasAdiabaticRemovalLimit_finiteLehmannLimitSum
        s hbar energyGap weight hhbar hregular
    · exact hasStaticLimit_finiteUnswitchedLehmannSum
        s hbar energyGap weight hhbar hregular

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]
variable (system : BoundedFreeSystem H)

/-- Static nonresonance for a finite pure-point response. Degenerate transitions are allowed when
their physical transition weight vanishes. -/
def PurePointStaticNonresonant
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) : Prop :=
  ∀ mn : ι × ι,
    purePointTransitionWeight system data A B mn = 0 ∨
      data.energy mn.1 - data.energy mn.2 ≠ 0

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
  simpa [finiteLehmannLimitSum, finiteUnswitchedLehmannSum] using
    finiteLehmannLimitSum_has_both_local_iterated_limits
      (s := Finset.univ)
      system.hbar
      (fun mn : ι × ι => data.energy mn.1 - data.energy mn.2)
      (purePointTransitionWeight system data A B)
      (ne_of_gt system.hbar_pos)
      (fun mn _ => hregular mn)

end
end LinearResponse
end QuantumTheory