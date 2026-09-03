import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CreationAnnihilation

set_option linter.style.header false

/-!
# Occupation toggling for completed fermionic CAR operators

Completed fermionic creation and annihilation operators are signed partial reindexings of the
occupation basis. The underlying occupation toggle and its equivalence live in the algebraic
occupation layer; this file adds the complex fermionic phase used by completed operators.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- The fermionic sign, regarded as a complex phase for completed-space operators. -/
def fermionPhase (i : Mode) (n : Occupation Mode) : ℂ :=
  fermionSign i n

@[simp]
theorem norm_fermionPhase (i : Mode) (n : Occupation Mode) :
    ‖fermionPhase i n‖ = 1 := by
  simp [fermionPhase, fermionSign]

end Fermionic
end SecondQuantization
