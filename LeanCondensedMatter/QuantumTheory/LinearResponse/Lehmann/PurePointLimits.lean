import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Limits
import LeanCondensedMatter.QuantumTheory.LinearResponse.PurePointFrequencyDomain
import LeanCondensedMatter.QuantumTheory.LinearResponse.InfiniteTimeAdiabatic

set_option linter.style.header false

/-! # Pure-point and physical response limits -/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory Filter Topology

noncomputable section

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
            (purePointTransitionData system data A B mn).frequencyTerm omega eta)
        (Finset.univ.sum fun mn : ι × ι =>
          (purePointTransitionData system data A B mn).frequencyTerm 0 0) ∧
      HasLocalAdiabaticThenStaticLimit
        (fun omega eta =>
          Finset.univ.sum fun mn : ι × ι =>
            (purePointTransitionData system data A B mn).frequencyTerm omega eta)
        (Finset.univ.sum fun mn : ι × ι =>
          (purePointTransitionData system data A B mn).frequencyTerm 0 0) := by
  simpa [LehmannTransitionData.frequencyTerm] using
    finset_frequencyTerm_has_both_local_iterated_limits
      (s := Finset.univ)
      system.hbar
      (purePointTransitionData system data A B)
      (ne_of_gt system.hbar_pos)
      (fun mn _ => hregular mn)

/-- A total real-rate extension of the finite pure-point physical susceptibility.

For `eta > 0`, this is exactly
`adiabaticFrequencyDomainSusceptibilityOfPositiveRate`.  At nonpositive rates it is defined by the
same finite Lehmann expression.  This continuation is used only to package limits; all physical
statements below approach zero through positive rates. -/
private noncomputable def finitePurePointPhysicalSusceptibilityExtension
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) : ℂ :=
  if hη : 0 < eta then
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
      (purePointNormalizedExpectation system data) A B omega eta hη
  else
    Finset.univ.sum fun mn : ι × ι =>
      (purePointTransitionData system data A B mn).frequencyTerm omega eta

/-- The total extension is globally equal to the finite Lehmann resolvent sum. -/
private theorem finitePurePointPhysicalSusceptibilityExtension_eq_finite_sum
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) :
    finitePurePointPhysicalSusceptibilityExtension system data A B omega eta =
      Finset.univ.sum fun mn : ι × ι =>
        (purePointTransitionData system data A B mn).frequencyTerm omega eta := by
  by_cases hη : 0 < eta
  · simp only [finitePurePointPhysicalSusceptibilityExtension, dite_eq_left hη]
    exact adiabaticFrequencyDomainSusceptibilityOfPositiveRate_purePoint_eq_finite_sum
      system data A B omega eta hη
  · simp [finitePurePointPhysicalSusceptibilityExtension, hη,
      LehmannTransitionData.frequencyTerm]

/-- The physical positive-rate susceptibility has both local nonresonant iterated limits after
passing to its canonical total extension.  Both orders have the same zero-rate static Lehmann
value. -/
private theorem finite_purePointPhysicalSusceptibility_has_both_local_iterated_limits
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H)
    (hregular : PurePointStaticNonresonant system data A B) :
    HasLocalStaticThenAdiabaticLimit
        (finitePurePointPhysicalSusceptibilityExtension system data A B)
        (Finset.univ.sum fun mn : ι × ι =>
          (purePointTransitionData system data A B mn).frequencyTerm 0 0) ∧
      HasLocalAdiabaticThenStaticLimit
        (finitePurePointPhysicalSusceptibilityExtension system data A B)
        (Finset.univ.sum fun mn : ι × ι =>
          (purePointTransitionData system data A B mn).frequencyTerm 0 0) := by
  let F : ℝ → ℝ → ℂ := fun omega eta =>
    Finset.univ.sum fun mn : ι × ι =>
      (purePointTransitionData system data A B mn).frequencyTerm omega eta
  have hfun : finitePurePointPhysicalSusceptibilityExtension system data A B = F := by
    funext omega eta
    rw [finitePurePointPhysicalSusceptibilityExtension_eq_finite_sum]
  rw [hfun]
  simpa [F, LehmannTransitionData.frequencyTerm] using
    finite_purePointLehmann_has_both_local_iterated_limits
      system data A B hregular

/-- For the actual finite-observation-time response, taking `T -> infinity` first and then either
local order of `omega -> 0` and `eta -> 0+` gives the same finite static Lehmann value. -/
theorem finiteTime_purePointPhysicalSusceptibility_has_both_local_three_stage_limits
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H)
    (hregular : PurePointStaticNonresonant system data A B) :
    HasLongTimeThenLocalStaticThenAdiabaticLimit
        (fun T omega eta =>
          finiteTimeAdiabaticFrequencyDomainSusceptibility system
            (purePointNormalizedExpectation system data) A B omega eta T)
        (Finset.univ.sum fun mn : ι × ι =>
          (purePointTransitionData system data A B mn).frequencyTerm 0 0) ∧
      HasLongTimeThenLocalAdiabaticThenStaticLimit
        (fun T omega eta =>
          finiteTimeAdiabaticFrequencyDomainSusceptibility system
            (purePointNormalizedExpectation system data) A B omega eta T)
        (Finset.univ.sum fun mn : ι × ι =>
          (purePointTransitionData system data A B mn).frequencyTerm 0 0) := by
  have hlimits :=
    finite_purePointPhysicalSusceptibility_has_both_local_iterated_limits
      system data A B hregular
  have hlong : ∀ omega eta, 0 < eta →
      Tendsto
        (fun T =>
          finiteTimeAdiabaticFrequencyDomainSusceptibility system
            (purePointNormalizedExpectation system data) A B omega eta T)
        atTop
        (𝓝 (finitePurePointPhysicalSusceptibilityExtension
          system data A B omega eta)) := by
    intro omega eta hη
    simp only [finitePurePointPhysicalSusceptibilityExtension, dite_eq_left hη]
    exact tendsto_finiteTimeAdiabaticFrequencyDomainSusceptibility_atTop_eq_fixedRate
      system (purePointNormalizedExpectation system data) A B omega eta hη
  exact ⟨⟨_, hlong, hlimits.1⟩, ⟨_, hlong, hlimits.2⟩⟩

end
end LinearResponse
end QuantumTheory
