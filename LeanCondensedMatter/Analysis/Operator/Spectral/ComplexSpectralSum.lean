import LeanCondensedMatter.Analysis.Operator.Spectral.ComplexEigenvectorFamily

set_option linter.style.header false

/-!
# Complex spectral sums for compact operators

This module defines absolute summability and the totalized spectral sum over the nonzero complex
eigenvalues of an operator, counted with eigenspace multiplicity. These definitions do not assume
symmetry or self-adjointness.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

/-- The nonzero complex eigenvalues of `T`, counted with eigenspace multiplicity, are absolutely
summable. -/
def HasSummableComplexEigenvalues (T : H →L[ℂ] H) : Prop :=
  Summable (fun a : ComplexEigenvectorIndex T => ‖a.1.1‖)

/-- The totalized sum of the indexed nonzero complex eigenvalues of `T`, counted with eigenspace
multiplicity. -/
noncomputable def complexSpectralSum (T : H →L[ℂ] H) : ℂ :=
  ∑' a : ComplexEigenvectorIndex T, a.1.1

/-- Absolute complex spectral summability implies summability of the complex eigenvalue series. -/
theorem summable_complexEigenvectorIndex (h : HasSummableComplexEigenvalues T) :
    Summable (fun a : ComplexEigenvectorIndex T => a.1.1) :=
  Summable.of_norm h

end ContinuousLinearMap
