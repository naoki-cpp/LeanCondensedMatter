import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TimeOrdering
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointWickDiagram
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TwoPoint

set_option linter.style.header false

/-!
# Fermionic external fields in imaginary time

This module connects the external labels used by two-point Wick diagrams to free imaginary-time
evolved creation and annihilation operators. It defines time ordering for arbitrary labelled
external fields and identifies the canonical annihilation/creation label pair with
`twoPointTimeOrderedProduct`.

For `τ < τ'`, reordering two odd external fields contributes the fermionic exchange sign through
`Common.timeOrderedProduct Statistics.fermion`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- The imaginary-time evolved operator represented by an external field label. -/
noncomputable def externalFieldOperator (ε : Mode → ℝ) (τ : ℝ) :
    ExternalFieldLabel Mode → OccupationFock Mode →ₗ[ℂ] OccupationFock Mode
  | .annihilation i => imaginaryTimeEvolve ε τ (annihilate i)
  | .creation i => imaginaryTimeEvolve ε τ (create i)

@[simp]
theorem externalFieldOperator_annihilation (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    externalFieldOperator ε τ (.annihilation i) = imaginaryTimeEvolve ε τ (annihilate i) :=
  rfl

@[simp]
theorem externalFieldOperator_creation (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    externalFieldOperator ε τ (.creation i) = imaginaryTimeEvolve ε τ (create i) :=
  rfl

/-- Explicit free evolution of an annihilation external field. -/
theorem externalFieldOperator_annihilation_eq_smul (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    externalFieldOperator ε τ (.annihilation i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i :=
  imaginaryTimeEvolve_annihilate ε τ i

/-- Explicit free evolution of a creation external field. -/
theorem externalFieldOperator_creation_eq_smul (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    externalFieldOperator ε τ (.creation i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i :=
  imaginaryTimeEvolve_create ε τ i

/-- Fermionic time ordering of two labelled external fields. -/
noncomputable def timeOrderedExternalFields (ε : Mode → ℝ)
    (A B : ExternalFieldLabel Mode) (τA τB : ℝ) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.timeOrderedProduct Common.Statistics.fermion
    (externalFieldOperator ε τA A) (externalFieldOperator ε τB B) τA τB

/-- The canonical annihilation/creation labels reproduce the diagram-independent two-point
operator. -/
@[simp]
theorem timeOrderedExternalFields_annihilation_creation (ε : Mode → ℝ)
    (i j : Mode) (τ τ' : ℝ) :
    timeOrderedExternalFields ε (.annihilation i) (.creation j) τ τ' =
      twoPointTimeOrderedProduct ε i j τ τ' :=
  rfl

/-- Swapping both external fields and their times produces the fermionic exchange sign. -/
theorem timeOrderedExternalFields_swap (ε : Mode → ℝ)
    (A B : ExternalFieldLabel Mode) (τA τB : ℝ) :
    timeOrderedExternalFields ε B A τB τA =
      (Common.Statistics.fermion.zetaInt : ℂ) •
        timeOrderedExternalFields ε A B τA τB := by
  exact Common.timeOrderedProduct_swap Common.Statistics.fermion _ _ τA τB

end Fermionic
end SecondQuantization
