import LeanCondensedMatter.SecondQuantization.Bosonic.OperatorAlgebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.QuarticVertexLabel

set_option linter.style.header false

/-!
# Bosonic quartic interaction vertices

A quartic vertex carries two creation modes and two annihilation modes. The operator order is fixed
as `a†_{create₁} a†_{create₂} a_{annihilate₂} a_{annihilate₁}`, matching the fermionic quartic
vertex convention while using bosonic ladder operators.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- Compatibility alias for the statistics-independent quartic vertex label. -/
abbrev QuarticVertexLabel (Mode : Type*) := Common.QuarticVertexLabel Mode

/-- The ordered bosonic quartic vertex operator. -/
noncomputable def quarticVertexOperator (q : QuarticVertexLabel Mode) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (create q.create₁).comp
    ((create q.create₂).comp ((annihilate q.annihilate₂).comp (annihilate q.annihilate₁)))

/-- The finite bosonic quartic interaction with coupling `g`. -/
noncomputable def quarticInteraction [Fintype Mode] (g : QuarticVertexLabel Mode → ℂ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  ∑ q, g q • quarticVertexOperator q

end Bosonic
end SecondQuantization
