import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.ExchangeAlgebra

set_option linter.style.header false

/-!
# Local legs of a bosonic quartic vertex

The statistics-independent local-leg order, modes, kinds, energy shifts, and operator constructor are
specialized to bosonic ladder operators here.  CCR coefficients and their physical consequences
remain owned by the bosonic layer.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqQuarticLocalLeg : DecidableEq Mode := Classical.decEq Mode

/-- The bosonic operator represented by a local leg of a quartic vertex. -/
noncomputable def quarticLocalLegOperator (q : QuarticVertexLabel Mode) :
    Fin 4 → FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.quarticLocalLegOperator create annihilate q

/-- The free-energy shift of a quartic local-leg operator. -/
noncomputable def quarticLocalLegEnergyShift (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) :
    Fin 4 → ℝ :=
  Common.quarticLocalLegEnergyShift ε q

/-- Every quartic local-leg operator is an eigenoperator of the free imaginary-time evolution. -/
theorem imaginaryTimeEvolve_quarticLocalLegOperator (ε : Mode → ℝ)
    (q : QuarticVertexLabel Mode) (l : Fin 4) (τ : ℝ) :
    imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l) =
      Complex.exp (((τ * quarticLocalLegEnergyShift ε q l : ℝ) : ℂ)) •
        quarticLocalLegOperator q l := by
  simpa [imaginaryTimeEvolve, quarticLocalLegOperator, quarticLocalLegEnergyShift] using
    (Common.heisenbergEvolve_quarticLocalLegOperator
      (freeEigenvalue ε) ε create annihilate q l τ
      (fun i => imaginaryTimeEvolve_create ε τ i)
      (fun i => imaginaryTimeEvolve_annihilate ε τ i))

/-- The reverse mixed CCR, `[aᵢ†, aⱼ] = -δᵢⱼ`. -/
theorem comm_create_annihilate (i j : Mode) :
    comm (create i) (annihilate j) =
      if i = j then -(LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) else 0 := by
  rw [show comm (create i) (annihilate j) = -comm (annihilate j) (create i) by
    simp only [comm]
    abel]
  rw [comm_annihilate_create]
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

/-- The scalar multiplying the identity in the commutator of two quartic local legs. Creation then
annihilation has coefficient `-1`; annihilation then creation has coefficient `1`. -/
def quarticLocalLegCommutatorCoeff (q q' : QuarticVertexLabel Mode) (l l' : Fin 4) : ℂ :=
  if Common.quarticLocalLegIsCreate l = Common.quarticLocalLegIsCreate l' then 0
  else if Common.quarticLocalLegMode q l = Common.quarticLocalLegMode q' l' then
    if Common.quarticLocalLegIsCreate l = true then -1 else 1
  else 0

/-- The ordinary commutator of two bosonic quartic local-leg operators is a scalar identity. -/
theorem comm_quarticLocalLegOperator (q q' : QuarticVertexLabel Mode) (l l' : Fin 4) :
    comm (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      quarticLocalLegCommutatorCoeff q q' l l' •
        (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) := by
  fin_cases l <;> fin_cases l' <;>
    simp [quarticLocalLegOperator, quarticLocalLegCommutatorCoeff,
      Common.quarticLocalLegOperator, Common.quarticLocalLegIsCreate,
      Common.quarticLocalLegMode, comm_create_create, comm_annihilate_annihilate,
      comm_annihilate_create, comm_create_annihilate]

/-- The Common `ζ`-commutator form of the bosonic quartic local-leg CCR. -/
theorem zetaCommutator_quarticLocalLegOperator (q q' : QuarticVertexLabel Mode)
    (l l' : Fin 4) :
    Common.zetaCommutator ((Common.Statistics.boson.zetaInt : ℤ) : ℂ)
        (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      quarticLocalLegCommutatorCoeff q q' l l' •
        (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) := by
  simpa [Common.zetaCommutator, Common.Statistics.zetaInt_boson, comm] using
    comm_quarticLocalLegOperator q q' l l'

end
end Bosonic
end SecondQuantization
