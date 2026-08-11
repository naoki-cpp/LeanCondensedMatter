import LeanCondensedMatter.QuantumTheory.DensityOperator.Expectation
import LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation

set_option linter.style.header false

/-!
# Density states as normalized expectations

This module supplies the canonical bridge from the physical density-operator API to the minimal
normalized expectation interface used by bounded linear response. Keeping the bridge upstream of
the Kubo formula lets response and conservation modules share one construction.
-/

namespace QuantumTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A density operator as the normalized expectation interface used by linear response. -/
noncomputable def DensityOperator.toNormalizedExpectation
    (ρ : DensityOperator H) : LinearResponse.NormalizedExpectation H where
  toContinuousLinearMap := ρ.expectation
  map_one := by
    change ρ.expectation (ContinuousLinearMap.id ℂ H) = 1
    exact ρ.expectation_id

@[simp]
theorem DensityOperator.toNormalizedExpectation_apply
    (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ρ.toNormalizedExpectation A = ρ.expectation A :=
  rfl

end
end QuantumTheory
