import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TimedField

set_option linter.style.header false

/-!
# Local legs of a quartic fermionic vertex

The statistics-independent local-leg order, modes, kinds, energy shifts, and operator constructor are
specialized to fermionic ladder operators here. Generic exchange algebra lives in `Common.Algebra`;
its quartic local-leg specialization is supplied separately by the Common interaction layer.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode]

/-! ## Local-leg operator semantics -/

/-- The fermionic operator represented by a local leg of a quartic vertex. -/
noncomputable def quarticLocalLegOperator (q : QuarticVertexLabel Mode) :
    Fin 4 → OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.quarticLocalLegOperator create annihilate q

/-- A local leg is an eigenoperator of the free imaginary-time evolution. -/
theorem imaginaryTimeEvolve_quarticLocalLegOperator (ε : Mode → ℝ) (q : QuarticVertexLabel Mode)
    (l : Fin 4) (τ : ℝ) :
    imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l) =
      Complex.exp (((τ * quarticLocalLegEnergyShift ε q l : ℝ) : ℂ)) •
        quarticLocalLegOperator q l := by
  simpa [imaginaryTimeEvolve, quarticLocalLegOperator, Common.quarticLocalLegOperator,
    quarticLocalLegEnergyShift] using
    (Common.QuarticLocalLeg.heisenbergEvolve_operator
      (fermionEnergy ε) ε create annihilate (Common.quarticLocalLeg q l) τ
      (fun i => imaginaryTimeEvolve_create ε τ i)
      (fun i => imaginaryTimeEvolve_annihilate ε τ i))

/-! ## External-field compatibility -/

/-- View a quartic local leg as an external-style annihilation or creation field label. -/
def quarticLocalLegExternalFieldLabel (leg : Common.QuarticLocalLeg Mode) :
    ExternalFieldLabel Mode :=
  match leg with
  | .create i => .creation i
  | .annihilate i => .annihilation i

@[simp]
theorem bareExternalFieldOperator_quarticLocalLegExternalFieldLabel
    (leg : Common.QuarticLocalLeg Mode) :
    bareExternalFieldOperator (quarticLocalLegExternalFieldLabel leg) =
      leg.operator create annihilate := by
  cases leg <;> rfl

omit [LinearOrder Mode] in
@[simp]
theorem externalFieldLabelEnergyShift_quarticLocalLegExternalFieldLabel
    (ε : Mode → ℝ) (leg : Common.QuarticLocalLeg Mode) :
    externalFieldLabelEnergyShift ε (quarticLocalLegExternalFieldLabel leg) =
      leg.energyShift ε := by
  cases leg <;> rfl

/-- The time-labelled field corresponding to a quartic local leg has the same evolved-operator
semantics as that leg. -/
theorem timedFieldOperator_quarticLocalLeg (ε : Mode → ℝ) (τ : ℝ)
    (leg : Common.QuarticLocalLeg Mode) :
    timedFieldOperator ε ⟨τ, quarticLocalLegExternalFieldLabel leg⟩ =
      imaginaryTimeEvolve ε τ (leg.operator create annihilate) := by
  rw [timedFieldOperator_eq_smul,
    bareExternalFieldOperator_quarticLocalLegExternalFieldLabel,
    externalFieldLabelEnergyShift_quarticLocalLegExternalFieldLabel]
  symm
  simpa [imaginaryTimeEvolve] using
    (Common.QuarticLocalLeg.heisenbergEvolve_operator
      (fermionEnergy ε) ε create annihilate leg τ
      (fun i => imaginaryTimeEvolve_create ε τ i)
      (fun i => imaginaryTimeEvolve_annihilate ε τ i))

end Fermionic
end SecondQuantization
