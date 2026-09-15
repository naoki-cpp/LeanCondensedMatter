import Mathlib.Data.Fintype.Sum

set_option linter.style.header false

/-!
# Fermionic field labels

Statistics-specific labels distinguishing annihilation and creation fields belong to the fermionic
algebra layer. They are used by imaginary-time operator semantics and by diagrammatics, so keeping
them below both layers avoids an imaginary-time dependency on diagram syntax.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- A labelled fermionic field, carrying either an annihilation or creation mode. -/
inductive ExternalFieldLabel (Mode : Type*) where
  | annihilation (mode : Mode)
  | creation (mode : Mode)
  deriving DecidableEq

/-- External field labels are equivalent to two tagged copies of the mode type. -/
def ExternalFieldLabel.equivSum : ExternalFieldLabel Mode ≃ Mode ⊕ Mode where
  toFun
    | .annihilation i => Sum.inl i
    | .creation i => Sum.inr i
  invFun
    | Sum.inl i => .annihilation i
    | Sum.inr i => .creation i
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

noncomputable instance ExternalFieldLabel.instFintype [Fintype Mode] :
    Fintype (ExternalFieldLabel Mode) :=
  Fintype.ofEquiv (Mode ⊕ Mode) ExternalFieldLabel.equivSum.symm

/-- The canonical external labels for `T c_i(τ) c_j†(τ')`: external slot `0` is annihilation
mode `i`, and external slot `1` is creation mode `j`. -/
def twoPointExternalLabels (i j : Mode) : Fin 2 → ExternalFieldLabel Mode :=
  fun e => if e = 0 then .annihilation i else .creation j

@[simp]
theorem twoPointExternalLabels_zero (i j : Mode) :
    twoPointExternalLabels i j 0 = ExternalFieldLabel.annihilation i := by
  simp [twoPointExternalLabels]

@[simp]
theorem twoPointExternalLabels_one (i j : Mode) :
    twoPointExternalLabels i j 1 = ExternalFieldLabel.creation j := by
  simp [twoPointExternalLabels]

end Fermionic
end SecondQuantization
