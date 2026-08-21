import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Basic

set_option linter.style.header false

/-!
# Coordinate projections on completed Fock space

A predicate on configurations determines a contractive coordinate projection on the generic
completed Fock space: retain the amplitude of a configuration exactly when the predicate holds.

This is the statistics-independent backend shared by completed-space constructions such as a
fermionic single-mode occupation projection and finite-mode truncation. Statistics-specific layers
keep only the predicates and their physical or combinatorial semantics.
-/

namespace SecondQuantization
namespace Common

open scoped ENNReal

noncomputable section

variable {Config : Type*}

/-- The linear coordinate mask associated with a predicate on configurations. -/
noncomputable def completedCoordinateProjectionLinear (P : Config → Prop) :
    CompletedFock Config →ₗ[ℂ] CompletedFock Config := by
  classical
  exact
    { toFun := fun ψ =>
        ⟨fun c => if P c then ψ c else 0,
          (lp.memℓp ψ).mono' fun c => by
            by_cases h : P c <;> simp [h]⟩
      map_add' := fun ψ φ => by
        apply lp.ext
        funext c
        by_cases h : P c <;> simp [h]
      map_smul' := fun a ψ => by
        apply lp.ext
        funext c
        by_cases h : P c <;> simp [h] }

@[simp]
theorem completedCoordinateProjectionLinear_apply (P : Config → Prop)
    (ψ : CompletedFock Config) (c : Config) :
    completedCoordinateProjectionLinear P ψ c = if P c then ψ c else 0 := by
  rfl

/-- The bounded coordinate projection associated with a predicate on configurations. Its operator
norm is at most one. -/
noncomputable def completedCoordinateProjection (P : Config → Prop) :
    CompletedFock Config →L[ℂ] CompletedFock Config := by
  classical
  exact (completedCoordinateProjectionLinear P).mkContinuous 1 fun ψ => by
    simpa only [one_mul] using
      lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
        (x := completedCoordinateProjectionLinear P ψ) (y := ψ) (fun c => by
          by_cases h : P c <;> simp [completedCoordinateProjectionLinear_apply, h])

@[simp]
theorem completedCoordinateProjection_apply (P : Config → Prop)
    (ψ : CompletedFock Config) (c : Config) :
    completedCoordinateProjection P ψ c = if P c then ψ c else 0 := by
  rfl

/-- Coordinate projections are contractive. -/
theorem norm_completedCoordinateProjection_le (P : Config → Prop) (ψ : CompletedFock Config) :
    ‖completedCoordinateProjection P ψ‖ ≤ ‖ψ‖ := by
  classical
  simpa only [one_mul] using
    lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
      (x := completedCoordinateProjection P ψ) (y := ψ) (fun c => by
        by_cases h : P c <;> simp [completedCoordinateProjection_apply, h])

/-- Coordinate projections are nonexpansive. -/
theorem dist_completedCoordinateProjection_le (P : Config → Prop)
    (ψ φ : CompletedFock Config) :
    dist (completedCoordinateProjection P ψ) (completedCoordinateProjection P φ) ≤ dist ψ φ := by
  simpa [dist_eq_norm, map_sub] using norm_completedCoordinateProjection_le P (ψ - φ)

/-- A canonical basis state survives a coordinate projection exactly when its configuration
satisfies the predicate. -/
@[simp]
theorem completedCoordinateProjection_basisState (P : Config → Prop) (c : Config) :
    completedCoordinateProjection P (completedBasisState c) =
      if P c then completedBasisState c else 0 := by
  classical
  apply lp.ext
  funext d
  by_cases hc : P c <;> by_cases hd : P d <;> by_cases hdc : d = c
  all_goals simp [completedCoordinateProjection_apply, hc, hd, hdc]

end
end Common
end SecondQuantization
