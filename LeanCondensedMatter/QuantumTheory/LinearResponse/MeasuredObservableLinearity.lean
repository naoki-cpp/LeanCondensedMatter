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

@[simp]
theorem heisenbergEvolution_add
    (A₁ A₂ : H →L[ℂ] H) (t : ℝ) :
    heisenbergEvolution system (A₁ + A₂) t =
      heisenbergEvolution system A₁ t + heisenbergEvolution system A₂ t := by
  simp [heisenbergEvolution, mul_add, add_mul]

@[simp]
theorem heisenbergEvolution_smul
    (c : ℂ) (A : H →L[ℂ] H) (t : ℝ) :
    heisenbergEvolution system (c • A) t =
      c • heisenbergEvolution system A t := by
  simp [heisenbergEvolution]

@[simp]
theorem commutatorSusceptibility_add_left
    (expectation : NormalizedExpectation H)
    (A₁ A₂ B : H →L[ℂ] H) (t s : ℝ) :
    commutatorSusceptibility system expectation (A₁ + A₂) B t s =
      commutatorSusceptibility system expectation A₁ B t s +
        commutatorSusceptibility system expectation A₂ B t s := by
  simp [commutatorSusceptibility, mul_add, add_mul]
  ring

@[simp]
theorem commutatorSusceptibility_smul_left
    (expectation : NormalizedExpectation H)
    (c : ℂ) (A B : H →L[ℂ] H) (t s : ℝ) :
    commutatorSusceptibility system expectation (c • A) B t s =
      c • commutatorSusceptibility system expectation A B t s := by
  simp [commutatorSusceptibility, smul_eq_mul]
  ring

@[simp]
theorem retardedSusceptibility_add_left
    (expectation : NormalizedExpectation H)
    (A₁ A₂ B : H →L[ℂ] H) (t s : ℝ) :
    retardedSusceptibility system expectation (A₁ + A₂) B t s =
      retardedSusceptibility system expectation A₁ B t s +
        retardedSusceptibility system expectation A₂ B t s := by
  by_cases h : s ≤ t
  · simp [retardedSusceptibility, h]
  · simp [retardedSusceptibility, h]

@[simp]
theorem retardedSusceptibility_smul_left
    (expectation : NormalizedExpectation H)
    (c : ℂ) (A B : H →L[ℂ] H) (t s : ℝ) :
    retardedSusceptibility system expectation (c • A) B t s =
      c • retardedSusceptibility system expectation A B t s := by
  by_cases h : s ≤ t
  · simp [retardedSusceptibility, h]
  · simp [retardedSusceptibility, h]

/-- With source and times fixed, retarded susceptibility is a complex-linear functional of the
measured observable. -/
noncomputable def retardedSusceptibilityMeasuredLinearMap
    (expectation : NormalizedExpectation H)
    (source : H →L[ℂ] H) (t s : ℝ) :
    (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun := fun measured =>
    retardedSusceptibility system expectation measured source t s
  map_add' := fun A₁ A₂ =>
    retardedSusceptibility_add_left system expectation A₁ A₂ source t s
  map_smul' := fun c A =>
    retardedSusceptibility_smul_left system expectation c A source t s

@[simp]
theorem retardedSusceptibilityMeasuredLinearMap_apply
    (expectation : NormalizedExpectation H)
    (source measured : H →L[ℂ] H) (t s : ℝ) :
    retardedSusceptibilityMeasuredLinearMap system expectation source t s measured =
      retardedSusceptibility system expectation measured source t s :=
  rfl

end
end LinearResponse
end QuantumTheory
