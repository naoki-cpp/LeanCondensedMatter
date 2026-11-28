import LeanCondensedMatter.Analysis.Algebra.FinsuppDiagonal
import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CCR
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeAlgebra

set_option linter.style.header false

/-!
# Bosonic number operator

The single-mode number operator is `N_i = a_i† a_i`. Its basis states have eigenvalue `n_i`, and
the concrete exchange-algebra instance below gives the reordering identity `a_i a_i† = id + N_i`.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqNumberOperator : DecidableEq Mode := Classical.decEq Mode

noncomputable instance exchangeAlgebra :
    Common.ExchangeAlgebra Common.Statistics.boson Mode (Occupation Mode) where
  annihilate := annihilate
  create := create
  annihilate_create i j := by
    simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_boson] using
      comm_annihilate_create i j
  annihilate_annihilate i j := by
    simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_boson] using
      comm_annihilate_annihilate i j
  create_create i j := by
    simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_boson] using
      comm_create_create i j

/-- The single-mode number operator `N_i = a_i† a_i`. -/
noncomputable def numberOperator (i : Mode) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (create i).comp (annihilate i)

/-- The number-operator eigenvalue equation `N_i |n⟩ = n_i |n⟩`. -/
theorem numberOperator_basisState (i : Mode) (n : Occupation Mode) :
    numberOperator i (basisState n) = (n i : ℂ) • basisState n :=
  create_annihilate_basisState_same i n

/-- The single-mode number operator is the basis-diagonal operator with occupation weight
`n ↦ n i`. This is the canonical bridge from `aᵢ† aᵢ` to the common diagonal-operator API. -/
theorem numberOperator_eq_diagonalOperator (i : Mode) :
    numberOperator i =
      Finsupp.diagonalOperator (fun n : Occupation Mode => (n i : ℂ)) := by
  apply Common.linearMap_ext_basisState
  intro n
  rw [Common.diagonalOperator_basisState]
  exact numberOperator_basisState i n

/-- The reordering identity `a_i a_i† = id + N_i`. -/
theorem annihilate_comp_create_self (i : Mode) :
    (annihilate i).comp (create i) =
      (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) + numberOperator i := by
  have h := Common.annihilate_comp_create_self (s := Common.Statistics.boson) (Config := Occupation Mode) i
  rwa [Common.Statistics.zetaInt_boson, Int.cast_one, one_smul] at h

end

end Bosonic
end SecondQuantization
