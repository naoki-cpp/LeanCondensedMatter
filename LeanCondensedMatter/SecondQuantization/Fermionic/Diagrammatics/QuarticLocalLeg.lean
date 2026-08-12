import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.ExchangeAlgebra

set_option linter.style.header false

/-!
# Local legs of a quartic fermionic vertex

The statistics-independent local-leg order, modes, kinds, energy shifts, and operator constructor are
specialized to fermionic ladder operators here.  CAR relations and their physical consequences
remain owned by the fermionic layer.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-! ## Local-leg operator semantics -/

/-- The fermionic operator represented by a local leg of a quartic vertex. -/
noncomputable def quarticLocalLegOperator (q : QuarticVertexLabel Mode) :
    Fin 4 → OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.quarticLocalLegOperator create annihilate q

/-- The free-energy shift of a quartic local-leg operator. -/
noncomputable def quarticLocalLegEnergyShift (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) :
    Fin 4 → ℝ :=
  Common.quarticLocalLegEnergyShift ε q

/-- A local leg is an eigenoperator of the free imaginary-time evolution. -/
theorem imaginaryTimeEvolve_quarticLocalLegOperator (ε : Mode → ℝ) (q : QuarticVertexLabel Mode)
    (l : Fin 4) (τ : ℝ) :
    imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l) =
      Complex.exp (((τ * quarticLocalLegEnergyShift ε q l : ℝ) : ℂ)) •
        quarticLocalLegOperator q l := by
  simpa [imaginaryTimeEvolve, quarticLocalLegOperator, quarticLocalLegEnergyShift] using
    (Common.heisenbergEvolve_quarticLocalLegOperator
      (fermionEnergy ε) ε create annihilate q l τ
      (fun i => imaginaryTimeEvolve_create ε τ i)
      (fun i => imaginaryTimeEvolve_annihilate ε τ i))

/-! ## The bare anticommutator/zeta-commutator of two local legs -/

/-- The mode on which a quartic local-leg operator acts. -/
def quarticLocalLegMode (q : QuarticVertexLabel Mode) : Fin 4 → Mode :=
  Common.quarticLocalLegMode q

/-- Whether a quartic local leg is a creation leg. -/
def quarticLocalLegIsCreate : Fin 4 → Bool :=
  Common.quarticLocalLegIsCreate

/-- The bare anticommutator of two local-leg operators. -/
theorem anticomm_quarticLocalLegOperator (q q' : QuarticVertexLabel Mode) (l l' : Fin 4) :
    anticomm (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      if quarticLocalLegIsCreate l = quarticLocalLegIsCreate l' then
        (0 : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode)
      else if quarticLocalLegMode q l = quarticLocalLegMode q' l' then LinearMap.id else 0 := by
  fin_cases l <;> fin_cases l' <;>
    simp [quarticLocalLegOperator, quarticLocalLegIsCreate, quarticLocalLegMode,
      Common.quarticLocalLegOperator, Common.quarticLocalLegIsCreate,
      Common.quarticLocalLegMode, anticomm_create_create, anticomm_annihilate_annihilate,
      anticomm_annihilate_create, anticomm_create_annihilate]

/-- The Common `ζ`-commutator form of the fermionic quartic local-leg CAR. -/
theorem zetaCommutator_quarticLocalLegOperator (q q' : QuarticVertexLabel Mode) (l l' : Fin 4) :
    Common.zetaCommutator ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ)
        (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      (if quarticLocalLegIsCreate l = quarticLocalLegIsCreate l' then (0 : ℂ)
       else if quarticLocalLegMode q l = quarticLocalLegMode q' l' then 1 else 0) •
        (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
  have hbridge : Common.zetaCommutator ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ)
      (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      anticomm (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') :=
    exchangeCommutator_fermion_eq_anticomm _ _
  rw [hbridge, anticomm_quarticLocalLegOperator]
  split_ifs <;> simp

end Fermionic
end SecondQuantization
