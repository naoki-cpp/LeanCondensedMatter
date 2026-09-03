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

private noncomputable def coordinateProjectionLinear (P : Config → Prop) :
    CompletedFock Config →ₗ[ℂ] CompletedFock Config := by
  classical
  exact
    { toFun := fun ψ =>
        ⟨fun c => if P c then ψ c else 0,
          (lp.memℓp ψ).mono' fun c => by
            by_cases h : P c <;> simp [h]⟩
      map_add' := fun ψ φ => by
        ext c
        change (if P c then ψ c + φ c else 0) =
          (if P c then ψ c else 0) + (if P c then φ c else 0)
        by_cases h : P c <;> simp [h]
      map_smul' := fun a ψ => by
        ext c
        change (if P c then a • ψ c else 0) = a • (if P c then ψ c else 0)
        by_cases h : P c <;> simp [h] }

/-- The bounded coordinate projection associated with a predicate on configurations. Its operator
norm is at most one. -/
noncomputable def completedCoordinateProjection (P : Config → Prop) :
    CompletedFock Config →L[ℂ] CompletedFock Config := by
  classical
  exact (coordinateProjectionLinear P).mkContinuous 1 fun ψ => by
    simpa only [one_mul] using
      lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
        (x := coordinateProjectionLinear P ψ) (y := ψ) (fun c => by
          by_cases h : P c <;> simp [coordinateProjectionLinear, h])

@[simp]
theorem completedCoordinateProjection_apply (P : Config → Prop) [DecidablePred P]
    (ψ : CompletedFock Config) (c : Config) :
    completedCoordinateProjection P ψ c = if P c then ψ c else 0 := by
  classical
  by_cases h : P c <;> simp [completedCoordinateProjection, coordinateProjectionLinear, h]

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
theorem completedCoordinateProjection_basisState (P : Config → Prop) [DecidablePred P]
    (c : Config) :
    completedCoordinateProjection P (completedBasisState c) =
      if P c then completedBasisState c else 0 := by
  classical
  by_cases hc : P c
  · simp only [hc, if_true]
    ext d
    by_cases hd : P d
    · simp [completedCoordinateProjection_apply, hd]
    · have hdc : d ≠ c := by
        intro h
        subst d
        exact hd hc
      simp [completedCoordinateProjection_apply, hd, hdc]
  · simp only [hc, if_false]
    ext d
    by_cases hd : P d
    · have hdc : d ≠ c := by
        intro h
        subst d
        exact hc hd
      simp [completedCoordinateProjection_apply, hd, hdc]
    · simp [completedCoordinateProjection_apply, hd]

end
end Common
end SecondQuantization
