import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Diagonal

set_option linter.style.header false

/-!
# Coordinate projections on completed Fock space

A predicate on configurations determines a contractive coordinate projection on the generic
completed Fock space: retain the amplitude of a configuration exactly when the predicate holds.

This is the indicator-weight specialization of bounded diagonal multiplication. Statistics-specific
layers keep only the predicates and their physical or combinatorial semantics.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*}

/-- The bounded coordinate projection associated with a predicate on configurations. Its operator
norm is at most one. -/
noncomputable def completedCoordinateProjection (P : Config → Prop) :
    CompletedFock Config →L[ℂ] CompletedFock Config := by
  classical
  exact completedBoundedDiagonalOperator (fun c => if P c then 1 else 0) zero_le_one fun c => by
    by_cases h : P c <;> simp [h]

@[simp]
theorem completedCoordinateProjection_apply (P : Config → Prop) [DecidablePred P]
    (ψ : CompletedFock Config) (c : Config) :
    completedCoordinateProjection P ψ c = if P c then ψ c else 0 := by
  classical
  rw [completedCoordinateProjection, completedBoundedDiagonalOperator_apply]
  by_cases h : P c <;> simp [h]

/-- Coordinate projections are contractive. -/
theorem norm_completedCoordinateProjection_le (P : Config → Prop) (ψ : CompletedFock Config) :
    ‖completedCoordinateProjection P ψ‖ ≤ ‖ψ‖ := by
  classical
  simpa only [completedCoordinateProjection, one_mul] using
    norm_completedBoundedDiagonalOperator_apply_le
      (w := fun c : Config => if P c then 1 else 0) zero_le_one
      (fun c => by by_cases h : P c <;> simp [h]) ψ

/-- Coordinate projections are nonexpansive. -/
theorem dist_completedCoordinateProjection_le (P : Config → Prop)
    (ψ φ : CompletedFock Config) :
    dist (completedCoordinateProjection P ψ) (completedCoordinateProjection P φ) ≤ dist ψ φ := by
  simpa [dist_eq_norm, map_sub] using norm_completedCoordinateProjection_le P (ψ - φ)

/-- A canonical basis state survives a coordinate projection exactly when its configuration
satisfies the predicate. -/
@[simp]
theorem completedCoordinateProjection_basisState (P : Config → Prop) [DecidablePred P]
    (c : Config) :
    completedCoordinateProjection P (completedBasisState c) =
      if P c then completedBasisState c else 0 := by
  classical
  by_cases hc : P c <;> simp [completedCoordinateProjection, hc]

end
end Common
end SecondQuantization
