import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator
import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteWeightedTrace

set_option linter.style.header false

/-!
# Weighted trace of the fermionic number operator

`Common.weightedTrace`, specialized to `numberOperator` — the one part of the old fermionic
weighted-diagonal wrapper that is genuinely fermionic content: an actual computation against
`numberOperator_basisState`, rather than a thin delegation to the Common finite weighted-trace
layer.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

theorem weightedTrace_numberOperator (w : Occupation Mode → ℂ) (i : Mode) :
    Common.weightedTrace w (numberOperator i) =
      ∑ n ∈ (Finset.univ : Finset (Occupation Mode)).filter (i ∈ ·), w n := by
  have h : ∀ n : Occupation Mode,
      Common.matrixCoeff (numberOperator i) n n = if i ∈ n then 1 else 0 := fun n => by
    rcases Finset.decidableMem i n with hi | hi
    · exact Common.matrixCoeff_of_smul_basisState
        (show numberOperator i (basisState n) = (0 : ℂ) • basisState n by
          rw [numberOperator_basisState, if_neg hi, zero_smul])
    · exact Common.matrixCoeff_of_smul_basisState
        (show numberOperator i (basisState n) = (1 : ℂ) • basisState n by
          rw [numberOperator_basisState, if_pos hi, one_smul])
  simp only [Common.weightedTrace, h, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]

end Fermionic
end SecondQuantization
