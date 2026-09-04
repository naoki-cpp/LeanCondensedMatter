import LeanCondensedMatter.QuantumTheory.LinearResponse.LehmannLimits

set_option linter.style.header false

/-!
# Physical finite-dimensional Lehmann limits

The fixed-positive-rate susceptibility carries a proof that the switching rate is positive, while
an iterated-limit predicate is most conveniently stated for a total function of the real rate.  For
a finite pure-point system, this module defines a canonical total extension: at positive rate it is
the physical susceptibility, and outside the physical region it is the finite Lehmann expression.
The values outside `eta > 0` do not affect any regulator-removal limit, whose source filter is
`nhdsWithin 0 (Ioi 0)`.

The finite-dimensional Lehmann equality proves that this extension is globally equal to the finite
resolvent sum.  Consequently the nonresonant limit theorem transfers directly to the physical
susceptibility.  Combining it with the finite-observation-time convergence theorem also gives both
three-stage orders with `T -> infinity` taken first.
-/

namespace QuantumTheory
namespace LinearResponse

open Set Filter Topology

noncomputable section

/-- Long time first, followed by the local static-then-adiabatic order. -/
def HasLongTimeThenLocalStaticThenAdiabaticLimit
    (F : ℝ → ℝ → ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ fixedRate : ℝ → ℝ → ℂ,
    (∀ omega eta, 0 < eta →
      Tendsto (fun T => F T omega eta) atTop (𝓝 (fixedRate omega eta))) ∧
    HasLocalStaticThenAdiabaticLimit fixedRate L

/-- Long time first, followed by the local adiabatic-then-static order. -/
def HasLongTimeThenLocalAdiabaticThenStaticLimit
    (F : ℝ → ℝ → ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ fixedRate : ℝ → ℝ → ℂ,
    (∀ omega eta, 0 < eta →
      Tendsto (fun T => F T omega eta) atTop (𝓝 (fixedRate omega eta))) ∧
    HasLocalAdiabaticThenStaticLimit fixedRate L

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]
variable (system : BoundedFreeSystem H)

/-- A total real-rate extension of the finite pure-point physical susceptibility.

For `eta > 0`, this is exactly
`adiabaticFrequencyDomainSusceptibilityOfPositiveRate`.  At nonpositive rates it is defined by the
same finite Lehmann expression.  This continuation is used only to package limits; all physical
statements below approach zero through positive rates. -/
noncomputable def finitePurePointPhysicalSusceptibilityExtension
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) : ℂ :=
  if hη : 0 < eta then
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
      (purePointNormalizedExpectation system data) A B omega eta hη
  else
    Finset.univ.sum fun mn : ι × ι =>
      lehmannTerm system.hbar omega eta
        (data.energy mn.1 - data.energy mn.2)
        (purePointTransitionWeight system data A B mn)

/-- On the physical positive-rate domain, the total extension is the actual switched
susceptibility. -/
theorem finitePurePointPhysicalSusceptibilityExtension_eq_physical_of_pos
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta) :
    finitePurePointPhysicalSusceptibilityExtension system data A B omega eta =
      adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
        (purePointNormalizedExpectation system data) A B omega eta hη := by
  simp only [finitePurePointPhysicalSusceptibilityExtension, dif_pos hη]

/-- The total extension is globally equal to the finite Lehmann resolvent sum. -/
theorem finitePurePointPhysicalSusceptibilityExtension_eq_finite_sum
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) :
    finitePurePointPhysicalSusceptibilityExtension system data A B omega eta =
      Finset.univ.sum fun mn : ι × ι =>
        lehmannTerm system.hbar omega eta
          (data.energy mn.1 - data.energy mn.2)
          (purePointTransitionWeight system data A B mn) := by
  by_cases hη : 0 < eta
  · rw [finitePurePointPhysicalSusceptibilityExtension_eq_physical_of_pos
      system data A B omega eta hη]
    exact adiabaticFrequencyDomainSusceptibilityOfPositiveRate_purePoint_eq_finite_sum
      system data A B omega eta hη
  · simp [finitePurePointPhysicalSusceptibilityExtension, hη]

/-- The physical positive-rate susceptibility has both local nonresonant iterated limits after
passing to its canonical total extension.  Both orders have the same zero-rate static Lehmann
value. -/
theorem finite_purePointPhysicalSusceptibility_has_both_local_iterated_limits
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H)
    (hregular : PurePointStaticNonresonant system data A B) :
    HasLocalStaticThenAdiabaticLimit
        (finitePurePointPhysicalSusceptibilityExtension system data A B)
        (Finset.univ.sum fun mn : ι × ι =>
          unswitchedLehmannTerm system.hbar 0
            (data.energy mn.1 - data.energy mn.2)
            (purePointTransitionWeight system data A B mn)) ∧
      HasLocalAdiabaticThenStaticLimit
        (finitePurePointPhysicalSusceptibilityExtension system data A B)
        (Finset.univ.sum fun mn : ι × ι =>
          unswitchedLehmannTerm system.hbar 0
            (data.energy mn.1 - data.energy mn.2)
            (purePointTransitionWeight system data A B mn)) := by
  convert finite_purePointLehmann_has_both_local_iterated_limits
    system data A B hregular using 1 <;>
    funext omega eta <;>
    exact finitePurePointPhysicalSusceptibilityExtension_eq_finite_sum
      system data A B omega eta

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
          unswitchedLehmannTerm system.hbar 0
            (data.energy mn.1 - data.energy mn.2)
            (purePointTransitionWeight system data A B mn)) ∧
      HasLongTimeThenLocalAdiabaticThenStaticLimit
        (fun T omega eta =>
          finiteTimeAdiabaticFrequencyDomainSusceptibility system
            (purePointNormalizedExpectation system data) A B omega eta T)
        (Finset.univ.sum fun mn : ι × ι =>
          unswitchedLehmannTerm system.hbar 0
            (data.energy mn.1 - data.energy mn.2)
            (purePointTransitionWeight system data A B mn)) := by
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
    rw [finitePurePointPhysicalSusceptibilityExtension_eq_physical_of_pos
      system data A B omega eta hη]
    exact tendsto_finiteTimeAdiabaticFrequencyDomainSusceptibility_atTop_eq_fixedRate
      system (purePointNormalizedExpectation system data) A B omega eta hη
  exact ⟨⟨_, hlong, hlimits.1⟩, ⟨_, hlong, hlimits.2⟩⟩

end
end LinearResponse
end QuantumTheory
