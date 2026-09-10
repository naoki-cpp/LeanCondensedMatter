import LeanCondensedMatter.Analysis.Operator.ZetaCommutator
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Interaction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations

set_option linter.style.header false

/-!
# Local legs of a quartic fermionic vertex

The statistics-independent local-leg order, modes, kinds, energy shifts, and operator constructor are
specialized to fermionic ladder operators here. CAR relations and their physical consequences
remain owned by the fermionic layer.
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
  simpa [imaginaryTimeEvolve, quarticLocalLegOperator] using
    (Common.heisenbergEvolve_quarticLocalLegOperator
      (fermionEnergy ε) ε create annihilate q l τ
      (fun i => imaginaryTimeEvolve_create ε τ i)
      (fun i => imaginaryTimeEvolve_annihilate ε τ i))

/-! ## The statistics-sign bracket of two local legs -/

/-- The statistics-sign form of the fermionic quartic local-leg CAR. -/
theorem zetaCommutator_quarticLocalLegOperator (q q' : QuarticVertexLabel Mode) (l l' : Fin 4) :
    LinearMap.zetaCommutator ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ)
        (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      (if quarticLocalLegIsCreate l = quarticLocalLegIsCreate l' then (0 : ℂ)
       else if quarticLocalLegMode q l = quarticLocalLegMode q' l' then 1 else 0) •
        (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
  fin_cases l <;> fin_cases l' <;>
    simp [quarticLocalLegOperator, Common.quarticLocalLegIsCreate,
      Common.quarticLocalLegMode, Common.quarticLocalLegOperator,
      Common.Statistics.zetaInt_fermion, anticomm_create_create,
      anticomm_annihilate_annihilate, anticomm_annihilate_create,
      anticomm_create_annihilate] <;> rfl

end Fermionic
end SecondQuantization
