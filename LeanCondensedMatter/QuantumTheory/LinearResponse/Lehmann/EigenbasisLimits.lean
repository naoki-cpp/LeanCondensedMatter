import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Limits
import LeanCondensedMatter.QuantumTheory.LinearResponse.EigenbasisFrequencyDomain
import LeanCondensedMatter.QuantumTheory.LinearResponse.InfiniteTimeAdiabatic

set_option linter.style.header false

/-! # Eigenbasis and physical response limits -/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]
variable (system : BoundedFreeSystem H)

/-- Static nonresonance for a finite eigenbasis response. Degenerate transitions are allowed when
their physical transition weight vanishes. -/
def EigenbasisStaticNonresonant
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) : Prop :=
  ∀ mn : ι × ι,
    (eigenbasisTransitionData system data A B mn).weight = 0 ∨
      (eigenbasisTransitionData system data A B mn).energyGap ≠ 0

/-- For the actual finite-observation-time response, taking `T -> infinity` first and then either
local order of `omega -> 0` and `eta -> 0+` gives the same finite static Lehmann value. -/
theorem finiteTime_eigenbasisPhysicalSusceptibility_has_both_local_three_stage_limits
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H)
    (hregular : EigenbasisStaticNonresonant system data A B) :
    HasLongTimeThenLocalStaticThenAdiabaticLimit
        (fun T omega eta =>
          finiteTimeAdiabaticFrequencyDomainSusceptibility system
            (eigenbasisNormalizedExpectation system data) A B omega eta T)
        (Finset.univ.sum fun mn : ι × ι =>
          (eigenbasisTransitionData system data A B mn).frequencyTerm 0 0) ∧
      HasLongTimeThenLocalAdiabaticThenStaticLimit
        (fun T omega eta =>
          finiteTimeAdiabaticFrequencyDomainSusceptibility system
            (eigenbasisNormalizedExpectation system data) A B omega eta T)
        (Finset.univ.sum fun mn : ι × ι =>
          (eigenbasisTransitionData system data A B mn).frequencyTerm 0 0) := by
  let F : ℝ → ℝ → ℂ := fun omega eta =>
    Finset.univ.sum fun mn : ι × ι =>
      (eigenbasisTransitionData system data A B mn).frequencyTerm omega eta
  have hlimits := finset_frequencyTerm_has_both_local_iterated_limits
    (s := Finset.univ) system.hbar (eigenbasisTransitionData system data A B)
    (ne_of_gt system.hbar_pos) (fun mn _ => hregular mn)
  have hlong : ∀ omega eta, 0 < eta →
      Tendsto
        (fun T =>
          finiteTimeAdiabaticFrequencyDomainSusceptibility system
            (eigenbasisNormalizedExpectation system data) A B omega eta T)
        atTop
        (𝓝 (F omega eta)) := by
    intro omega eta hη
    have hlong := tendsto_finiteTimeAdiabaticFrequencyDomainSusceptibility_atTop
      system (eigenbasisNormalizedExpectation system data) A B omega eta hη
    rw [adiabaticFrequencyDomainSusceptibility_eigenbasis_eq_finite_sum
      system data A B omega eta hη] at hlong
    exact hlong
  exact ⟨⟨_, hlong, hlimits.1⟩, ⟨_, hlong, hlimits.2⟩⟩

end
end LinearResponse
end QuantumTheory
