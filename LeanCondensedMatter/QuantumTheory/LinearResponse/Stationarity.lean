import LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation
import LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics

set_option linter.style.header false

/-!
# Stationary expectations for bounded free dynamics

This module owns invariance of normalized expectations under free Heisenberg evolution. It depends
on the independent expectation-functional and free-dynamics layers, without making either one own
the other.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (system : BoundedFreeSystem H)

/-- Stationarity means invariance under the free Heisenberg evolution. -/
def IsStationary (expectation : NormalizedExpectation H) : Prop :=
  ∀ t A, expectation (heisenbergEvolution system A t) = expectation A

/-- Every normalized expectation is invariant at the initial time. -/
theorem expectation_heisenbergEvolution_zero (expectation : NormalizedExpectation H)
    (A : H →L[ℂ] H) :
    expectation (heisenbergEvolution system A 0) = expectation A := by
  simp

end
end LinearResponse
end QuantumTheory
