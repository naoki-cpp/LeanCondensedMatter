import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TimeOrdering
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointWickDiagram
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# Fermionic external fields in imaginary time

This module connects the external labels used by two-point Wick diagrams to the existing
imaginary-time evolved creation and annihilation operators.  It also defines the canonical
fermionic time-ordered two-point operator.

The convention is

```text
Tτ cᵢ(τ) cⱼ†(τ')
```

with the annihilation field supplied first.  For `τ < τ'`, reordering contributes the fermionic
exchange sign through `Common.timeOrderedProduct Statistics.fermion`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode]

/-- The imaginary-time evolved operator represented by an external field label. -/
noncomputable def externalFieldOperator (ε : Mode → ℝ) (τ : ℝ) :
    ExternalFieldLabel Mode → FockSpace Mode →ₗ[ℂ] FockSpace Mode
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
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.timeOrderedProduct Common.Statistics.fermion
    (externalFieldOperator ε τA A) (externalFieldOperator ε τB B) τA τB

/-- Canonical two-point operator `Tτ cᵢ(τ) cⱼ†(τ')`. -/
noncomputable def twoPointTimeOrderedProduct (ε : Mode → ℝ)
    (i j : Mode) (τ τ' : ℝ) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  timeOrderedExternalFields ε (.annihilation i) (.creation j) τ τ'

/-- When the annihilation field is later, it remains on the left. -/
theorem twoPointTimeOrderedProduct_of_gt (ε : Mode → ℝ) (i j : Mode)
    {τ τ' : ℝ} (h : τ' < τ) :
    twoPointTimeOrderedProduct ε i j τ τ' =
      (externalFieldOperator ε τ (.annihilation i)).comp
        (externalFieldOperator ε τ' (.creation j)) := by
  exact Common.timeOrderedProduct_of_gt Common.Statistics.fermion _ _ h

/-- When the creation field is later, the two odd fields are exchanged with the fermionic sign. -/
theorem twoPointTimeOrderedProduct_of_lt (ε : Mode → ℝ) (i j : Mode)
    {τ τ' : ℝ} (h : τ < τ') :
    twoPointTimeOrderedProduct ε i j τ τ' =
      (Common.Statistics.fermion.zetaInt : ℂ) •
        ((externalFieldOperator ε τ' (.creation j)).comp
          (externalFieldOperator ε τ (.annihilation i))) := by
  exact Common.timeOrderedProduct_of_lt Common.Statistics.fermion _ _ h

/-- At equal imaginary times, the project convention uses the symmetric `θ(0) = 1/2` value. -/
@[simp]
theorem twoPointTimeOrderedProduct_self_time (ε : Mode → ℝ) (i j : Mode) (τ : ℝ) :
    twoPointTimeOrderedProduct ε i j τ τ =
      (2⁻¹ : ℂ) •
        ((externalFieldOperator ε τ (.annihilation i)).comp
            (externalFieldOperator ε τ (.creation j)) +
          (Common.Statistics.fermion.zetaInt : ℂ) •
            ((externalFieldOperator ε τ (.creation j)).comp
              (externalFieldOperator ε τ (.annihilation i)))) := by
  exact Common.timeOrderedProduct_self_time Common.Statistics.fermion _ _ τ

/-- Swapping both external fields and their times produces the fermionic exchange sign. -/
theorem timeOrderedExternalFields_swap (ε : Mode → ℝ)
    (A B : ExternalFieldLabel Mode) (τA τB : ℝ) :
    timeOrderedExternalFields ε B A τB τA =
      (Common.Statistics.fermion.zetaInt : ℂ) •
        timeOrderedExternalFields ε A B τA τB := by
  exact Common.timeOrderedProduct_swap Common.Statistics.fermion _ _ τA τB

end Fermionic
end SecondQuantization
