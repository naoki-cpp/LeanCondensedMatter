import LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation.Basic
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Unitary

set_option linter.style.header false

/-!
# Stationary expectations for unitary-group dynamics

This module owns invariance of normalized expectations under free Heisenberg evolution. It depends
on the independent expectation-functional and free-dynamics layers, without making either one own
the other.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))

/-- Stationarity means invariance under the free Heisenberg evolution. -/
def IsStationary (expectation : NormalizedExpectation H) : Prop :=
  ∀ t A, expectation (heisenbergEvolution U t A) = expectation A

/-- Stationarity moves a relative-time evolution from the right factor to the left factor
of a two-point product. No self-adjointness or generator assumption is required. -/
theorem IsStationary.expectation_mul_heisenbergEvolution_neg
    {expectation : NormalizedExpectation H} (h : IsStationary U expectation)
    (A B : H →L[ℂ] H) (t : ℝ) :
    expectation (A * heisenbergEvolution U (-t) B) =
      expectation (heisenbergEvolution U t A * B) := by
  symm
  simpa only [map_mul, heisenbergEvolution_heisenbergEvolution,
    neg_add_cancel, heisenbergEvolution_zero] using
    h t (A * heisenbergEvolution U (-t) B)

end
end LinearResponse
end QuantumTheory
