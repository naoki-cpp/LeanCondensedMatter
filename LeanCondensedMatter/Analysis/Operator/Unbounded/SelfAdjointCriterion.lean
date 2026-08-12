import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option linter.style.header false

/-!
# Self-adjointness criteria for partial linear operators

This module collects generic Hilbert-space criteria for proving self-adjointness of densely defined
partial linear operators. The results are independent of any concrete quantum-mechanical
realization.

For a densely defined symmetric operator `A`, formal adjointness gives `A ≤ A†`. Therefore proving
self-adjointness reduces to the reverse domain inclusion `A†.domain ≤ A.domain`.
-/

namespace LinearPMap

noncomputable section

open Set
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

private theorem isSelfAdjoint_of_isFormalAdjoint_of_adjoint_domain_le
    (hdense : Dense ((A.domain : Submodule ℂ H) : Set H))
    (hsymm : A.IsFormalAdjoint A)
    (hdom : A.adjoint.domain ≤ A.domain) :
    IsSelfAdjoint A := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hle : A ≤ A.adjoint := hsymm.le_adjoint hdense
  have hdomain : A.domain = A.adjoint.domain := le_antisymm hle.1 hdom
  exact (LinearPMap.eq_of_le_of_domain_eq hle hdomain).symm

/-- For a densely defined symmetric partial operator, self-adjointness is equivalent to the reverse
adjoint-domain inclusion. The forward inclusion is already supplied by symmetry. -/
theorem isSelfAdjoint_iff_adjoint_domain_le_of_isFormalAdjoint
    (hdense : Dense ((A.domain : Submodule ℂ H) : Set H))
    (hsymm : A.IsFormalAdjoint A) :
    IsSelfAdjoint A ↔ A.adjoint.domain ≤ A.domain := by
  constructor
  · intro hself
    have hadj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hself
    rw [hadj]
  · intro hdom
    exact isSelfAdjoint_of_isFormalAdjoint_of_adjoint_domain_le hdense hsymm hdom

end

end LinearPMap
