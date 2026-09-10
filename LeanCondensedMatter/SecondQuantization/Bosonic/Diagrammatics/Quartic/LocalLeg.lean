import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Interaction
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic

set_option linter.style.header false

/-!
# Local legs of a bosonic quartic vertex

The statistics-independent local-leg order, modes, kinds, energy shifts, and operator constructor are
specialized to bosonic ladder operators here. Exchange algebra is owned by the Common quartic layer.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*}

/-- The bosonic operator represented by a local leg of a quartic vertex. -/
noncomputable def quarticLocalLegOperator (q : QuarticVertexLabel Mode) :
    Fin 4 → FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.quarticLocalLegOperator create annihilate q

/-- Every quartic local-leg operator is an eigenoperator of the free imaginary-time evolution. -/
theorem imaginaryTimeEvolve_quarticLocalLegOperator (ε : Mode → ℝ)
    (q : QuarticVertexLabel Mode) (l : Fin 4) (τ : ℝ) :
    imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l) =
      Complex.exp (((τ * Common.quarticLocalLegEnergyShift ε q l : ℝ) : ℂ)) •
        quarticLocalLegOperator q l := by
  simpa [imaginaryTimeEvolve, quarticLocalLegOperator] using
    (Common.heisenbergEvolve_quarticLocalLegOperator
      (freeEigenvalue ε) ε create annihilate q l τ
      (fun i => imaginaryTimeEvolve_create ε τ i)
      (fun i => imaginaryTimeEvolve_annihilate ε τ i))

end
end Bosonic
end SecondQuantization
