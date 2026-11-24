import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TimeOrdering
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.FieldLabel
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# Fermionic external fields in imaginary time

This module connects the fermionic external-field labels to free imaginary-time evolved creation and
annihilation operators. It defines time ordering for arbitrary labelled external fields.

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

/-- Scalar relating the physical dispersion to the dispersion shifted by μ for one
charged external field. -/
noncomputable def externalFieldChemicalPotentialFactor (μ τ : ℝ) :
    ExternalFieldLabel Mode → ℂ
  | .annihilation _ => Complex.exp (-(τ : ℂ) * (μ : ℂ))
  | .creation _ => Complex.exp ((τ : ℂ) * (μ : ℂ))

/-- A uniform energy shift contributes the scalar of the field's particle-number charge. -/
theorem externalFieldOperator_eq_shiftedDispersion
    (ε : Mode → ℝ) (μ τ : ℝ) (label : ExternalFieldLabel Mode) :
    externalFieldOperator ε τ label =
      externalFieldChemicalPotentialFactor μ τ label •
        externalFieldOperator (fun k => ε k - μ) τ label := by
  cases label with
  | annihilation i =>
      change externalFieldOperator ε τ (.annihilation i) =
        Complex.exp (-(τ : ℂ) * (μ : ℂ)) •
          externalFieldOperator (fun k => ε k - μ) τ (.annihilation i)
      rw [externalFieldOperator_annihilation_eq_smul,
        externalFieldOperator_annihilation_eq_smul, smul_smul, ← Complex.exp_add]
      congr 1
      congr 1
      push_cast
      ring
  | creation i =>
      change externalFieldOperator ε τ (.creation i) =
        Complex.exp ((τ : ℂ) * (μ : ℂ)) •
          externalFieldOperator (fun k => ε k - μ) τ (.creation i)
      rw [externalFieldOperator_creation_eq_smul,
        externalFieldOperator_creation_eq_smul, smul_smul, ← Complex.exp_add]
      congr 1
      congr 1
      push_cast
      ring

/-- Fermionic time ordering of two labelled external fields. -/
noncomputable def timeOrderedExternalFields (ε : Mode → ℝ)
    (A B : ExternalFieldLabel Mode) (τA τB : ℝ) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.timeOrderedProduct Common.Statistics.fermion
    (externalFieldOperator ε τA A) (externalFieldOperator ε τB B) τA τB

end Fermionic
end SecondQuantization
