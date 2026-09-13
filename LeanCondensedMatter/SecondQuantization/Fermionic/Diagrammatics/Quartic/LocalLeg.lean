import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Interaction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution

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
  simpa [imaginaryTimeEvolve, quarticLocalLegOperator] using
    (Common.heisenbergEvolve_quarticLocalLegOperator
      (fermionEnergy ε) ε create annihilate q l τ
      (fun i => imaginaryTimeEvolve_create ε τ i)
      (fun i => imaginaryTimeEvolve_annihilate ε τ i))

end Fermionic
end SecondQuantization