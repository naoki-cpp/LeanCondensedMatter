import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Toggle

set_option linter.style.header false

/-!
# Bounded operators on completed fermionic Fock space

This file lifts the occupation toggle equivalence to the completed `ℓ²` representation. The toggle
is the common isometric reindexing underlying fermionic creation and annihilation operators.
-/

namespace SecondQuantization
namespace Fermionic

open scoped ENNReal

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

/-- Reindex an `ℓ²` occupation amplitude by toggling mode `i`. -/
noncomputable def completedToggleLinear (i : Mode) :
    CompletedFockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode where
  toFun ψ := by
    refine ⟨fun n => ψ (toggleOccupation i n), ?_⟩
    apply memℓp_gen
    have hψ := (lp.memℓp ψ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa [Function.comp_def, toggleOccupationEquiv_apply] using
      hψ.comp_injective (toggleOccupationEquiv i).injective
  map_add' ψ φ := by
    apply lp.ext
    funext n
    rfl
  map_smul' c ψ := by
    apply lp.ext
    funext n
    rfl

@[simp]
theorem completedToggleLinear_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedToggleLinear i ψ n = ψ (toggleOccupation i n) :=
  rfl

/-- Toggling occupation coordinates preserves the `ℓ²` norm. -/
theorem norm_completedToggleLinear (i : Mode) (ψ : CompletedFockSpace Mode) :
    ‖completedToggleLinear i ψ‖ = ‖ψ‖ := by
  have hrpow :
      ‖completedToggleLinear i ψ‖ ^ (2 : ℝ) = ‖ψ‖ ^ (2 : ℝ) := by
    rw [lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num),
      lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)]
    simpa [completedToggleLinear_apply, toggleOccupationEquiv_apply] using
      (Equiv.tsum_eq (toggleOccupationEquiv i)
        (fun n : Occupation Mode => ‖ψ n‖ ^ (2 : ℝ)))
  have hsq : ‖completedToggleLinear i ψ‖ ^ (2 : ℕ) = ‖ψ‖ ^ (2 : ℕ) := by
    simpa [Real.rpow_natCast] using hrpow
  nlinarith [norm_nonneg (completedToggleLinear i ψ), norm_nonneg ψ]

/-- The occupation toggle as a continuous linear isometry. -/
noncomputable def completedToggle (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  (completedToggleLinear i).mkContinuous (1 : ℝ) fun ψ => by
    rw [norm_completedToggleLinear]
    simp

@[simp]
theorem completedToggle_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedToggle i ψ n = ψ (toggleOccupation i n) :=
  rfl

@[simp]
theorem completedToggle_completedToggle (i : Mode) (ψ : CompletedFockSpace Mode) :
    completedToggle i (completedToggle i ψ) = ψ := by
  apply lp.ext
  funext n
  rw [completedToggle_apply, completedToggle_apply, toggleOccupation_involutive i n]

end
end Fermionic
end SecondQuantization
