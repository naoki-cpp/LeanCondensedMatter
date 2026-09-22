import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Interaction

set_option linter.style.header false

/-!
# Local legs of a bosonic quartic vertex

The statistics-independent local-leg order, modes, kinds, energy shifts, and operator constructor are
specialized to bosonic ladder operators here. Generic exchange algebra lives in `Common.Algebra`;
its quartic local-leg specialization is supplied separately by the Common interaction layer.
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

end
end Bosonic
end SecondQuantization
