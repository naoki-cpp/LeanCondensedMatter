import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.ExchangeAlgebra

set_option linter.style.header false

/-!
# Local legs of a quartic fermionic vertex

Operators, energy shifts, modes, and CAR relations for the four local legs.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode]

/-! ## Local-leg operator semantics -/

/-- **The operator a vertex's local leg `Fin 4` stands for**, matching `WickDiagram.lean`'s fixed
local-leg convention `0 ↦ create₁, 1 ↦ create₂, 2 ↦ annihilate₂, 3 ↦ annihilate₁` exactly. -/
noncomputable def quarticLocalLegOperator (q : QuarticVertexLabel Mode) :
    Fin 4 → FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  ![create q.create₁, create q.create₂, annihilate q.annihilate₂, annihilate q.annihilate₁]

/-- **The free-evolution eigenvalue shift** of a vertex's local leg — the exponent
`imaginaryTimeEvolve_quarticLocalLegOperator` below rescales that leg's operator by, matching each
local leg's sign convention (`+ε` for a creation operator, `-ε` for an annihilation operator). -/
noncomputable def quarticLocalLegEnergyShift (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) :
    Fin 4 → ℝ :=
  ![ε q.create₁, ε q.create₂, -ε q.annihilate₂, -ε q.annihilate₁]

/-- **A local leg's operator evolves as a pure eigenvector** under `imaginaryTimeEvolve`, with
eigenvalue shift `quarticLocalLegEnergyShift`. The single fact tying `quarticLocalLegOperator`'s
four cases to `imaginaryTimeEvolve_create`/`imaginaryTimeEvolve_annihilate`. -/
theorem imaginaryTimeEvolve_quarticLocalLegOperator (ε : Mode → ℝ) (q : QuarticVertexLabel Mode)
    (l : Fin 4) (τ : ℝ) :
    imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l) =
      Complex.exp (((τ * quarticLocalLegEnergyShift ε q l : ℝ) : ℂ)) •
        quarticLocalLegOperator q l := by
  fin_cases l <;>
    simp [quarticLocalLegOperator, quarticLocalLegEnergyShift, imaginaryTimeEvolve_create,
      imaginaryTimeEvolve_annihilate, mul_comm]

/-! ## The bare anticommutator/zeta-commutator of two local legs -/

/-- **The mode a local leg's ladder operator acts on** — companion to `quarticLocalLegOperator`'s
own `0 ↦ create₁, 1 ↦ create₂, 2 ↦ annihilate₂, 3 ↦ annihilate₁` convention. -/
def quarticLocalLegMode (q : QuarticVertexLabel Mode) : Fin 4 → Mode :=
  ![q.create₁, q.create₂, q.annihilate₂, q.annihilate₁]

/-- **Whether a local leg is a creation leg** (`0, 1`) or an annihilation leg (`2, 3`). -/
def quarticLocalLegIsCreate : Fin 4 → Bool := ![true, true, false, false]

/-- **The bare anticommutator of two local leg operators**, at possibly different vertex labels:
`0` if both legs are the same kind (both creation or both annihilation — CAR's
`anticomm_create_create`/`anticomm_annihilate_annihilate`, *always* `0`, even at the same mode),
and otherwise `δ` on the two legs' modes (CAR's `anticomm_annihilate_create`/
`anticomm_create_annihilate`) — a single closed formula covering same-vertex ("tadpole") and
cross-vertex leg pairs alike, since `quarticLocalLegMode`/`quarticLocalLegOperator` only depend on
the vertex label supplied, not on any shared vertex identity. -/
theorem anticomm_quarticLocalLegOperator (q q' : QuarticVertexLabel Mode) (l l' : Fin 4) :
    anticomm (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      if quarticLocalLegIsCreate l = quarticLocalLegIsCreate l' then
        (0 : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
      else if quarticLocalLegMode q l = quarticLocalLegMode q' l' then LinearMap.id else 0 := by
  fin_cases l <;> fin_cases l' <;>
    simp [quarticLocalLegOperator, quarticLocalLegIsCreate, quarticLocalLegMode,
      anticomm_create_create, anticomm_annihilate_annihilate, anticomm_annihilate_create,
      anticomm_create_annihilate]

/-- **The general theorem's zeta-commutator hypothesis, for a single vertex's four legs** —
`Common.zetaCommutator` at `ζ := Statistics.fermion.zetaInt` is exactly `anticomm`
(`exchangeCommutator_fermion_eq_anticomm`), so `anticomm_quarticLocalLegOperator` transfers
directly. -/
theorem zetaCommutator_quarticLocalLegOperator (q q' : QuarticVertexLabel Mode) (l l' : Fin 4) :
    Common.zetaCommutator ((Statistics.fermion.zetaInt : ℤ) : ℂ)
        (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      (if quarticLocalLegIsCreate l = quarticLocalLegIsCreate l' then (0 : ℂ)
       else if quarticLocalLegMode q l = quarticLocalLegMode q' l' then 1 else 0) •
        (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) := by
  have hbridge : Common.zetaCommutator ((Statistics.fermion.zetaInt : ℤ) : ℂ)
      (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      anticomm (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') :=
    exchangeCommutator_fermion_eq_anticomm _ _
  rw [hbridge, anticomm_quarticLocalLegOperator]
  split_ifs <;> simp

end Fermionic
end SecondQuantization
