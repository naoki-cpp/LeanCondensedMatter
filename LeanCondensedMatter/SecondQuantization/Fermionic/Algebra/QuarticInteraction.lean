import LeanCondensedMatter.SecondQuantization.Common.Interaction.Quartic
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CreationAnnihilation

set_option linter.style.header false

/-!
# Fermionic quartic interaction operators

This module owns the statistics-specific algebraic realization of the generic quartic interaction
constructors using fermionic creation and annihilation operators. No imaginary-time or diagrammatic
structure is used here.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

export Common (QuarticVertexLabel)

/-- The quartic vertex operator, in fixed creation-creation-annihilation-annihilation order. -/
noncomputable def quarticVertexOperator (q : Common.QuarticVertexLabel Mode) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.quarticVertexOperator create annihilate q

/-- A fermionic quartic interaction supported on a finite set of vertex labels. -/
noncomputable def quarticInteractionOn (support : Finset (Common.QuarticVertexLabel Mode))
    (g : Common.QuarticVertexLabel Mode → ℂ) : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.quarticInteractionOn support create annihilate g

/-- The all-label quartic interaction on a finite mode type. -/
noncomputable def quarticInteraction [Fintype Mode] (g : Common.QuarticVertexLabel Mode → ℂ) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.quarticInteraction create annihilate g

end Fermionic
end SecondQuantization
