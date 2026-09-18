import LeanCondensedMatter.Analysis.Operator.ZetaCommutator
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ExternalField

set_option linter.style.header false

/-!
# Time-labelled fermionic external fields

This module owns statistics-specific semantics for a single creation or annihilation field carrying
an imaginary-time coordinate. It packages the field label with its time, exposes the corresponding
free-evolved operator and energy shift, and proves the scalar zeta-commutator and free-evolution
eigenoperator laws used by thermal pairing expansions.

These declarations are independent of any particular two-point or diagram representation.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode]

/-- A single creation or annihilation field together with its imaginary time. -/
structure TimedField (Mode : Type*) where
  /-- The imaginary time attached to the field. -/
  time : ℝ
  /-- The creation or annihilation label carried by the field. -/
  label : ExternalFieldLabel Mode

/-- The mode carried by an external fermionic field label. -/
private def externalFieldLabelMode : ExternalFieldLabel Mode → Mode
  | .annihilation i => i
  | .creation i => i

/-- Whether an external fermionic field label is a creation field. -/
private def externalFieldLabelIsCreate : ExternalFieldLabel Mode → Bool
  | .annihilation _ => false
  | .creation _ => true

/-- The bare creation or annihilation operator represented by an external field label. -/
noncomputable def bareExternalFieldOperator :
    ExternalFieldLabel Mode → OccupationFock Mode →ₗ[ℂ] OccupationFock Mode
  | .annihilation i => annihilate i
  | .creation i => create i

/-- The free-evolution eigenvalue shift of an external field label. -/
def externalFieldLabelEnergyShift (ε : Mode → ℝ) : ExternalFieldLabel Mode → ℝ
  | .annihilation i => -ε i
  | .creation i => ε i

/-- A time-labelled field as an evolved linear operator. -/
noncomputable def timedFieldOperator (ε : Mode → ℝ)
    (field : TimedField Mode) : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  externalFieldOperator ε field.time field.label

/-- Every evolved external field is its bare ladder operator times the expected exponential. -/
theorem externalFieldOperator_eq_smul_bare (ε : Mode → ℝ) (τ : ℝ)
    (label : ExternalFieldLabel Mode) :
    externalFieldOperator ε τ label =
      Complex.exp (((τ * externalFieldLabelEnergyShift ε label : ℝ) : ℂ)) •
        bareExternalFieldOperator label := by
  cases label with
  | annihilation i =>
      rw [externalFieldOperator_annihilation_eq_smul]
      change Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i =
        Complex.exp (((τ * -ε i : ℝ) : ℂ)) • annihilate i
      congr 2
      push_cast
      ring
  | creation i =>
      rw [externalFieldOperator_creation_eq_smul]
      change Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i =
        Complex.exp (((τ * ε i : ℝ) : ℂ)) • create i
      congr 2
      push_cast
      ring

/-- The bare fermionic zeta-commutator of two labelled fields is a scalar identity operator. -/
private theorem zetaCommutator_bareExternalFieldOperator
    (A B : ExternalFieldLabel Mode) :
    LinearMap.zetaCommutator ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ)
        (bareExternalFieldOperator A) (bareExternalFieldOperator B) =
      (if externalFieldLabelIsCreate A = externalFieldLabelIsCreate B then (0 : ℂ)
       else if externalFieldLabelMode A = externalFieldLabelMode B then 1 else 0) •
        (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
  cases A <;> cases B <;>
    simp [bareExternalFieldOperator, externalFieldLabelIsCreate, externalFieldLabelMode,
      Common.Statistics.zetaInt_fermion, anticomm_annihilate_annihilate,
      anticomm_annihilate_create, anticomm_create_annihilate, anticomm_create_create] <;>
    split <;> simp_all

/-- The scalar coefficient in the zeta-commutator of two evolved fields. -/
noncomputable def timedFieldCommutatorCoeff (ε : Mode → ℝ)
    (A B : TimedField Mode) : ℂ :=
  Complex.exp (((A.time * externalFieldLabelEnergyShift ε A.label : ℝ) : ℂ)) *
    Complex.exp (((B.time * externalFieldLabelEnergyShift ε B.label : ℝ) : ℂ)) *
    (if externalFieldLabelIsCreate A.label = externalFieldLabelIsCreate B.label then (0 : ℂ)
     else if externalFieldLabelMode A.label = externalFieldLabelMode B.label then 1 else 0)

/-- A time-labelled field has the expected scalar-times-bare normal form. -/
theorem timedFieldOperator_eq_smul (ε : Mode → ℝ) (field : TimedField Mode) :
    timedFieldOperator ε field =
      Complex.exp (((field.time * externalFieldLabelEnergyShift ε field.label : ℝ) : ℂ)) •
        bareExternalFieldOperator field.label :=
  externalFieldOperator_eq_smul_bare ε field.time field.label

/-- Two evolved fields satisfy the scalar zeta-commutator hypothesis. -/
theorem zetaCommutator_timedFieldOperator (ε : Mode → ℝ)
    (A B : TimedField Mode) :
    LinearMap.zetaCommutator ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ)
        (timedFieldOperator ε A) (timedFieldOperator ε B) =
      timedFieldCommutatorCoeff ε A B •
        (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
  rw [timedFieldOperator_eq_smul, timedFieldOperator_eq_smul,
    LinearMap.zetaCommutator_smul_smul, zetaCommutator_bareExternalFieldOperator, smul_smul,
    timedFieldCommutatorCoeff]

/-- A time-labelled field remains an eigenoperator after a further evolution by `-β`. -/
theorem heisenbergEvolve_timedFieldOperator (ε : Mode → ℝ) (β : ℝ)
    (field : TimedField Mode) :
    Common.heisenbergEvolve (fermionEnergy ε) (-β) (timedFieldOperator ε field) =
      Complex.exp (((externalFieldLabelEnergyShift ε field.label * (-β) : ℝ) : ℂ)) •
        timedFieldOperator ε field := by
  obtain ⟨τ, label⟩ := field
  cases label with
  | annihilation i =>
      change Common.heisenbergEvolve (fermionEnergy ε) (-β)
          (imaginaryTimeEvolve ε τ (annihilate i)) =
        Complex.exp ((((-ε i) * (-β) : ℝ) : ℂ)) •
          imaginaryTimeEvolve ε τ (annihilate i)
      have step : Common.heisenbergEvolve (fermionEnergy ε) (-β)
          (imaginaryTimeEvolve ε τ (annihilate i)) =
        imaginaryTimeEvolve ε (τ + -β) (annihilate i) :=
        Common.heisenbergEvolve_heisenbergEvolve (fermionEnergy ε) τ (-β) (annihilate i)
      rw [step, imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_annihilate, smul_smul,
        ← Complex.exp_add]
      congr 2
      push_cast
      ring
  | creation i =>
      change Common.heisenbergEvolve (fermionEnergy ε) (-β)
          (imaginaryTimeEvolve ε τ (create i)) =
        Complex.exp ((((ε i) * (-β) : ℝ) : ℂ)) • imaginaryTimeEvolve ε τ (create i)
      have step : Common.heisenbergEvolve (fermionEnergy ε) (-β)
          (imaginaryTimeEvolve ε τ (create i)) =
        imaginaryTimeEvolve ε (τ + -β) (create i) :=
        Common.heisenbergEvolve_heisenbergEvolve (fermionEnergy ε) τ (-β) (create i)
      rw [step, imaginaryTimeEvolve_create, imaginaryTimeEvolve_create, smul_smul,
        ← Complex.exp_add]
      congr 2
      push_cast
      ring

end Fermionic
end SecondQuantization
