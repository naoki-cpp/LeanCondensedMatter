import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.ExchangeAlgebra

set_option linter.style.header false

/-!
# Local legs of a bosonic quartic vertex

Operators, free-energy shifts, modes, and CCR constants for the four local legs. The local-leg order
matches the fermionic diagram convention: two creation legs followed by the two annihilation legs in
operator-composition order.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

local instance instDecidableEqQuarticLocalLeg : DecidableEq Mode := Classical.decEq Mode

/-- The bosonic operator represented by a local leg of a quartic vertex. -/
noncomputable def quarticLocalLegOperator (q : QuarticVertexLabel Mode) :
    Fin 4 → FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  ![create q.create₁, create q.create₂, annihilate q.annihilate₂, annihilate q.annihilate₁]

/-- The free-energy shift of a quartic local-leg operator. -/
noncomputable def quarticLocalLegEnergyShift (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) :
    Fin 4 → ℝ :=
  ![ε q.create₁, ε q.create₂, -ε q.annihilate₂, -ε q.annihilate₁]

/-- Every quartic local-leg operator is an eigenoperator of the free imaginary-time evolution. -/
theorem imaginaryTimeEvolve_quarticLocalLegOperator (ε : Mode → ℝ)
    (q : QuarticVertexLabel Mode) (l : Fin 4) (τ : ℝ) :
    imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l) =
      Complex.exp (((τ * quarticLocalLegEnergyShift ε q l : ℝ) : ℂ)) •
        quarticLocalLegOperator q l := by
  fin_cases l <;>
    simp [quarticLocalLegOperator, quarticLocalLegEnergyShift, imaginaryTimeEvolve_create,
      imaginaryTimeEvolve_annihilate, mul_comm]

/-- The mode on which a quartic local-leg operator acts. -/
def quarticLocalLegMode (q : QuarticVertexLabel Mode) : Fin 4 → Mode :=
  ![q.create₁, q.create₂, q.annihilate₂, q.annihilate₁]

/-- Whether a quartic local leg is a creation leg. -/
def quarticLocalLegIsCreate : Fin 4 → Bool :=
  ![true, true, false, false]

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
  if quarticLocalLegIsCreate l = quarticLocalLegIsCreate l' then 0
  else if quarticLocalLegMode q l = quarticLocalLegMode q' l' then
    if quarticLocalLegIsCreate l = true then -1 else 1
  else 0

/-- The ordinary commutator of two bosonic quartic local-leg operators is a scalar identity. -/
theorem comm_quarticLocalLegOperator (q q' : QuarticVertexLabel Mode) (l l' : Fin 4) :
    comm (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      quarticLocalLegCommutatorCoeff q q' l l' •
        (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) := by
  fin_cases l <;> fin_cases l' <;>
    simp [quarticLocalLegOperator, quarticLocalLegCommutatorCoeff, quarticLocalLegIsCreate,
      quarticLocalLegMode, comm_create_create, comm_annihilate_annihilate,
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

end Bosonic
end SecondQuantization
