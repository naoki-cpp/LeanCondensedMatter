import LeanCondensedMatter.SecondQuantization.Fermionic.WeightedDiagonalFunctional

set_option linter.style.header false

/-!
# Weighted traces of the fermionic number operators

`WeightedDiagonalFunctional.lean`'s `weightedTrace`, specialized to `numberOperator`/
`totalNumberOperator` — split out from that file since it is the one part of the wrapper that is
genuinely fermionic content (an actual computation against `numberOperator_basisState`/
`totalNumberOperator_basisState`), rather than a thin `Common.WeightedDiagonalFunctional`
delegation.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

theorem weightedTrace_numberOperator (w : FermionOccupation Mode → ℂ) (i : Mode) :
    weightedTrace w (numberOperator i) =
      ∑ n ∈ (Finset.univ : Finset (FermionOccupation Mode)).filter (i ∈ ·), w n := by
  have h : ∀ n : FermionOccupation Mode,
      Common.matrixCoeff (numberOperator i) n n = if i ∈ n then 1 else 0 := fun n => by
    rcases Finset.decidableMem i n with hi | hi
    · exact matrixCoeff_of_smul_basisState (by
        rw [numberOperator_basisState, if_neg hi, if_neg hi, zero_smul])
    · exact matrixCoeff_of_smul_basisState (by
        rw [numberOperator_basisState, if_pos hi, if_pos hi, one_smul])
  simp only [weightedTrace, Common.weightedTrace, h, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]

omit [LinearOrder Mode] in
theorem weightedTrace_totalNumberOperator (w : FermionOccupation Mode → ℂ) :
    weightedTrace w totalNumberOperator =
      ∑ n : FermionOccupation Mode, (fermionParticleNumber n : ℂ) * w n := by
  have h : ∀ n : FermionOccupation Mode,
      Common.matrixCoeff totalNumberOperator n n = (fermionParticleNumber n : ℂ) :=
    fun n => matrixCoeff_of_smul_basisState (totalNumberOperator_basisState n)
  simp only [weightedTrace, Common.weightedTrace, h]
  exact Finset.sum_congr rfl fun n _ => mul_comm _ _

end SecondQuantization
