import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Toggle

set_option linter.style.header false

/-!
# Bounded operators on completed fermionic Fock space

This file lifts occupation-basis reindexing to the completed `ℓ²` representation and uses it to
construct the bounded fermionic creation and annihilation operators. Both ladder maps are a
unit-modulus fermionic phase times the occupation toggle, restricted to the appropriate output
sector.
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
    ext n
    rfl
  map_smul' c ψ := by
    ext n
    rfl

@[simp]
theorem completedToggleLinear_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedToggleLinear i ψ n = ψ (toggleOccupation i n) :=
  rfl

@[simp]
theorem completedToggleLinear_completedToggleLinear (i : Mode)
    (ψ : CompletedFockSpace Mode) :
    completedToggleLinear i (completedToggleLinear i ψ) = ψ := by
  ext n
  rw [completedToggleLinear_apply, completedToggleLinear_apply,
    toggleOccupation_involutive i n]

private theorem norm_completedToggleLinear_le (i : Mode) (ψ : CompletedFockSpace Mode) :
    ‖completedToggleLinear i ψ‖ ≤ ‖ψ‖ := by
  apply lp.norm_le_of_tsum_le (p := (2 : ℝ≥0∞)) (by norm_num) (norm_nonneg ψ)
  rw [lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) ψ]
  exact le_of_eq <| by
    simpa [completedToggleLinear_apply, toggleOccupationEquiv_apply] using
      (Equiv.tsum_eq (toggleOccupationEquiv i)
        (fun n : Occupation Mode => ‖ψ n‖ ^ (2 : ℝ≥0∞).toReal))

/-- Toggling occupation coordinates preserves the `ℓ²` norm. -/
theorem norm_completedToggleLinear (i : Mode) (ψ : CompletedFockSpace Mode) :
    ‖completedToggleLinear i ψ‖ = ‖ψ‖ := by
  apply le_antisymm (norm_completedToggleLinear_le i ψ)
  simpa only [completedToggleLinear_completedToggleLinear] using
    norm_completedToggleLinear_le i (completedToggleLinear i ψ)

/-- The occupation toggle as a norm-preserving continuous linear map. -/
noncomputable def completedToggle (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  (completedToggleLinear i).mkContinuous (1 : ℝ) fun ψ => by
    simpa [norm_completedToggleLinear]

@[simp]
theorem completedToggle_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedToggle i ψ n = ψ (toggleOccupation i n) :=
  rfl

@[simp]
theorem completedToggle_completedToggle (i : Mode) (ψ : CompletedFockSpace Mode) :
    completedToggle i (completedToggle i ψ) = ψ := by
  ext n
  rw [completedToggle_apply, completedToggle_apply, toggleOccupation_involutive i n]

/-- The completed fermionic creation map before continuity is bundled. At output occupation `n`,
creation reads the amplitude at the toggled (hence unoccupied) source configuration, multiplies by
the source fermionic phase, and vanishes unless `i` is occupied in `n`. -/
noncomputable def completedCreateLinear (i : Mode) :
    CompletedFockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode where
  toFun ψ := by
    refine ⟨fun n => if i ∈ n then fermionPhase i (toggleOccupation i n) *
      ψ (toggleOccupation i n) else 0, ?_⟩
    exact (lp.memℓp (completedToggleLinear i ψ)).mono' fun n => by
      by_cases h : i ∈ n
      · simp [h, norm_fermionPhase]
      · simp [h]
  map_add' ψ φ := by
    ext n
    change (if i ∈ n then fermionPhase i (toggleOccupation i n) *
      (ψ + φ) (toggleOccupation i n) else 0) =
      (if i ∈ n then fermionPhase i (toggleOccupation i n) *
        ψ (toggleOccupation i n) else 0) +
      (if i ∈ n then fermionPhase i (toggleOccupation i n) *
        φ (toggleOccupation i n) else 0)
    by_cases h : i ∈ n
    · rw [toggleOccupation_of_mem h]
      simp [h, mul_add]
    · simp [h]
  map_smul' c ψ := by
    ext n
    change (if i ∈ n then fermionPhase i (toggleOccupation i n) *
      (c • ψ) (toggleOccupation i n) else 0) =
      c * (if i ∈ n then fermionPhase i (toggleOccupation i n) *
        ψ (toggleOccupation i n) else 0)
    by_cases h : i ∈ n
    · rw [toggleOccupation_of_mem h]
      simp [h, mul_left_comm]
    · simp [h]

@[simp]
theorem completedCreateLinear_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedCreateLinear i ψ n =
      if i ∈ n then fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n) else 0 :=
  rfl

/-- The completed fermionic annihilation map before continuity is bundled. It is the complementary
output-sector restriction of the same signed occupation toggle. -/
noncomputable def completedAnnihilateLinear (i : Mode) :
    CompletedFockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode where
  toFun ψ := by
    refine ⟨fun n => if i ∈ n then 0 else fermionPhase i (toggleOccupation i n) *
      ψ (toggleOccupation i n), ?_⟩
    exact (lp.memℓp (completedToggleLinear i ψ)).mono' fun n => by
      by_cases h : i ∈ n
      · simp [h]
      · simp [h, norm_fermionPhase]
  map_add' ψ φ := by
    ext n
    change (if i ∈ n then 0 else fermionPhase i (toggleOccupation i n) *
      (ψ + φ) (toggleOccupation i n)) =
      (if i ∈ n then 0 else fermionPhase i (toggleOccupation i n) *
        ψ (toggleOccupation i n)) +
      (if i ∈ n then 0 else fermionPhase i (toggleOccupation i n) *
        φ (toggleOccupation i n))
    by_cases h : i ∈ n
    · simp [h]
    · rw [toggleOccupation_of_not_mem h]
      simp [h, mul_add]
  map_smul' c ψ := by
    ext n
    change (if i ∈ n then 0 else fermionPhase i (toggleOccupation i n) *
      (c • ψ) (toggleOccupation i n)) =
      c * (if i ∈ n then 0 else fermionPhase i (toggleOccupation i n) *
        ψ (toggleOccupation i n))
    by_cases h : i ∈ n
    · simp [h]
    · rw [toggleOccupation_of_not_mem h]
      simp [h, mul_left_comm]

@[simp]
theorem completedAnnihilateLinear_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedAnnihilateLinear i ψ n =
      if i ∈ n then 0 else fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n) :=
  rfl

private theorem norm_completedCreateLinear_le (i : Mode) (ψ : CompletedFockSpace Mode) :
    ‖completedCreateLinear i ψ‖ ≤ ‖ψ‖ := by
  calc
    ‖completedCreateLinear i ψ‖ ≤ ‖completedToggleLinear i ψ‖ :=
      lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num) fun n => by
        by_cases h : i ∈ n
        · simp [completedCreateLinear_apply, completedToggleLinear_apply, h, norm_fermionPhase]
        · simp [completedCreateLinear_apply, completedToggleLinear_apply, h]
    _ = ‖ψ‖ := norm_completedToggleLinear i ψ

private theorem norm_completedAnnihilateLinear_le (i : Mode) (ψ : CompletedFockSpace Mode) :
    ‖completedAnnihilateLinear i ψ‖ ≤ ‖ψ‖ := by
  calc
    ‖completedAnnihilateLinear i ψ‖ ≤ ‖completedToggleLinear i ψ‖ :=
      lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num) fun n => by
        by_cases h : i ∈ n
        · simp [completedAnnihilateLinear_apply, completedToggleLinear_apply, h]
        · simp [completedAnnihilateLinear_apply, completedToggleLinear_apply, h,
            norm_fermionPhase]
    _ = ‖ψ‖ := norm_completedToggleLinear i ψ

/-- Bounded fermionic creation on completed Fock space. -/
noncomputable def completedCreate (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  (completedCreateLinear i).mkContinuous 1 fun ψ => by
    simpa only [one_mul] using norm_completedCreateLinear_le i ψ

/-- Bounded fermionic annihilation on completed Fock space. -/
noncomputable def completedAnnihilate (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  (completedAnnihilateLinear i).mkContinuous 1 fun ψ => by
    simpa only [one_mul] using norm_completedAnnihilateLinear_le i ψ

@[simp]
theorem completedCreate_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedCreate i ψ n =
      if i ∈ n then fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n) else 0 :=
  rfl

@[simp]
theorem completedAnnihilate_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedAnnihilate i ψ n =
      if i ∈ n then 0 else fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n) :=
  rfl

end
end Fermionic
end SecondQuantization
