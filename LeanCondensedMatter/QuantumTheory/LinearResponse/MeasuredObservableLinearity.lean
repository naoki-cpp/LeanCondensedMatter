import LeanCondensedMatter.QuantumTheory.LinearResponse.RetardedSusceptibility

set_option linter.style.header false

/-!
# Linearity in the measured observable

The generic retarded susceptibility is linear in its measured-observable argument.  This module
packages that fact without introducing transport-specific terminology, so downstream conservation
and current adapters can compose an observable-valued linear map directly with the Kubo kernel.

The source-coupling observable remains fixed here.  No current, conductivity, or localization
convention is assumed.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- With source and times fixed, retarded susceptibility is a complex-linear functional of the
measured observable. -/
noncomputable def retardedSusceptibilityMeasuredLinearMap
    (expectation : NormalizedExpectation H)
    (source : H →L[ℂ] H) (t s : ℝ) :
    (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun := fun measured =>
    retardedSusceptibility system expectation measured source t s
  map_add' := fun A₁ A₂ => by
    by_cases h : s ≤ t
    · simp [retardedSusceptibility, commutatorSusceptibility, heisenbergEvolution,
        h, mul_add, add_mul]
      ring
    · simp [retardedSusceptibility, h]
  map_smul' := fun c A => by
    by_cases h : s ≤ t
    · simp [retardedSusceptibility, commutatorSusceptibility, heisenbergEvolution,
        h, smul_eq_mul]
      ring
    · simp [retardedSusceptibility, h]

end
end LinearResponse
end QuantumTheory
