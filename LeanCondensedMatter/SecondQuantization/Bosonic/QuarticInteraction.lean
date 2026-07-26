import LeanCondensedMatter.SecondQuantization.Common.QuarticVertexLabel
import LeanCondensedMatter.SecondQuantization.Bosonic.OperatorAlgebra.CreationAnnihilation

set_option linter.style.header false

/-!
# Bosonic quartic interaction vertices

This module realizes the statistics-independent `Common.QuarticVertexLabel` as a bosonic operator.
The operator ordering matches the fermionic quartic interaction convention, while the concrete
creation and annihilation maps come from the bosonic operator algebra.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- The bosonic quartic vertex operator
`a†_{q.create₁} a†_{q.create₂} a_{q.annihilate₂} a_{q.annihilate₁}`. -/
noncomputable def quarticVertexOperator (q : Common.QuarticVertexLabel Mode) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (create q.create₁).comp
    ((create q.create₂).comp ((annihilate q.annihilate₂).comp (annihilate q.annihilate₁)))

end Bosonic
end SecondQuantization
