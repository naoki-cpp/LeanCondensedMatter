import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.Interaction.Quartic

set_option linter.style.header false

/-!
# Bosonic quartic interaction vertices

A quartic vertex carries two creation modes and two annihilation modes. The operator order is fixed
as `a†_{create₁} a†_{create₂} a_{annihilate₂} a_{annihilate₁}`, matching the fermionic quartic
vertex convention while using bosonic ladder operators. The statistics-independent constructors
are inherited from `SecondQuantization.Common`.

For an infinite mode type, `quarticInteractionOn support g` constructs the operator from a finite set
of active quartic labels. The all-label `quarticInteraction g` remains the finite-mode specialization.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*}

export Common (QuarticVertexLabel)

/-- The ordered bosonic quartic vertex operator. -/
noncomputable def quarticVertexOperator (q : Common.QuarticVertexLabel Mode) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.quarticVertexOperator create annihilate q

/-- A bosonic quartic interaction supported on a finite set of vertex labels. -/
noncomputable def quarticInteractionOn (support : Finset (Common.QuarticVertexLabel Mode))
    (g : Common.QuarticVertexLabel Mode → ℂ) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.quarticInteractionOn support create annihilate g

/-- The all-label bosonic quartic interaction on a finite mode type. -/
noncomputable def quarticInteraction [Fintype Mode] (g : Common.QuarticVertexLabel Mode → ℂ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.quarticInteraction create annihilate g

end Bosonic
end SecondQuantization
