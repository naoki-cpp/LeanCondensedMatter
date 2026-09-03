import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CreationAnnihilation

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

/-- The fermionic sign, regarded as a complex phase for completed-space operators. -/
def fermionPhase (i : Mode) (n : Occupation Mode) : ℂ :=
  fermionSign i n

@[simp]
theorem norm_fermionPhase (i : Mode) (n : Occupation Mode) :
    ‖fermionPhase i n‖ = 1 := by
  simp [fermionPhase, fermionSign]

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

private noncomputable def completedSignedToggleLinear (i : Mode) :
    CompletedFockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode where
  toFun ψ := by
    refine ⟨fun n => fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n), ?_⟩
    exact (lp.memℓp (completedToggleLinear i ψ)).mono' fun n => by
      simp [completedToggleLinear_apply, norm_fermionPhase]
  map_add' ψ φ := by
    ext n
    change fermionPhase i (toggleOccupation i n) *
        ((ψ + φ) (toggleOccupation i n)) =
      fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n) +
        fermionPhase i (toggleOccupation i n) * φ (toggleOccupation i n)
    simp [mul_add]
  map_smul' c ψ := by
    ext n
    change fermionPhase i (toggleOccupation i n) *
        (c * ψ (toggleOccupation i n)) =
      c * (fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n))
    ring

@[simp]
private theorem completedSignedToggleLinear_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedSignedToggleLinear i ψ n =
      fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n) :=
  rfl

private theorem norm_completedSignedToggleLinear_le (i : Mode) (ψ : CompletedFockSpace Mode) :
    ‖completedSignedToggleLinear i ψ‖ ≤ ‖ψ‖ := by
  calc
    ‖completedSignedToggleLinear i ψ‖ ≤ ‖completedToggleLinear i ψ‖ :=
      lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num) fun n => by
        simp [completedSignedToggleLinear_apply, completedToggleLinear_apply, norm_fermionPhase]
    _ = ‖ψ‖ := norm_completedToggleLinear i ψ

private noncomputable def completedSignedToggle (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  (completedSignedToggleLinear i).mkContinuous 1 fun ψ => by
    simpa only [one_mul] using norm_completedSignedToggleLinear_le i ψ

@[simp]
private theorem completedSignedToggle_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedSignedToggle i ψ n =
      fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n) :=
  rfl

private noncomputable def completedCreateMap (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  (Common.completedCoordinateProjection (fun n : Occupation Mode => i ∈ n)).comp
    (completedSignedToggle i)

private noncomputable def completedAnnihilateMap (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  (Common.completedCoordinateProjection (fun n : Occupation Mode => i ∉ n)).comp
    (completedSignedToggle i)

/-- The completed fermionic creation map before continuity is bundled. At output occupation `n`,
creation reads the amplitude at the toggled (hence unoccupied) source configuration, multiplies by
the source fermionic phase, and vanishes unless `i` is occupied in `n`. -/
noncomputable def completedCreateLinear (i : Mode) :
    CompletedFockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedCreateMap i).toLinearMap

@[simp]
theorem completedCreateLinear_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedCreateLinear i ψ n =
      if i ∈ n then fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n) else 0 := by
  classical
  simp [completedCreateLinear, completedCreateMap, completedSignedToggle_apply,
    Common.completedCoordinateProjection_apply]

/-- The completed fermionic annihilation map before continuity is bundled. It is the complementary
output-sector restriction of the same signed occupation toggle. -/
noncomputable def completedAnnihilateLinear (i : Mode) :
    CompletedFockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedAnnihilateMap i).toLinearMap

@[simp]
theorem completedAnnihilateLinear_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedAnnihilateLinear i ψ n =
      if i ∈ n then 0 else fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n) := by
  classical
  simp [completedAnnihilateLinear, completedAnnihilateMap, completedSignedToggle_apply,
    Common.completedCoordinateProjection_apply]

/-- Bounded fermionic creation on completed Fock space. -/
noncomputable def completedCreate (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  completedCreateMap i

/-- Bounded fermionic annihilation on completed Fock space. -/
noncomputable def completedAnnihilate (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  completedAnnihilateMap i

@[simp]
theorem completedCreate_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedCreate i ψ n =
      if i ∈ n then fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n) else 0 := by
  classical
  simp [completedCreate, completedCreateMap, completedSignedToggle_apply,
    Common.completedCoordinateProjection_apply]

@[simp]
theorem completedAnnihilate_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedAnnihilate i ψ n =
      if i ∈ n then 0 else fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n) := by
  classical
  simp [completedAnnihilate, completedAnnihilateMap, completedSignedToggle_apply,
    Common.completedCoordinateProjection_apply]

private theorem completedSignedToggle_basisState (i : Mode) (n : Occupation Mode) :
    completedSignedToggle i (completedBasisState n) =
      fermionPhase i n • completedBasisState (toggleOccupation i n) := by
  classical
  ext m
  rw [completedSignedToggle_apply]
  by_cases hm : m = toggleOccupation i n
  · subst m
    rw [toggleOccupation_involutive]
    simp
  · have ht : toggleOccupation i m ≠ n := by
      intro h
      apply hm
      calc
        m = toggleOccupation i (toggleOccupation i m) :=
          (toggleOccupation_involutive i m).symm
        _ = toggleOccupation i n := congrArg (toggleOccupation i) h
    simp [completedBasisState_apply_of_ne hm, completedBasisState_apply_of_ne ht]

@[simp]
theorem completedCreate_basisState_of_mem {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    completedCreate i (completedBasisState n) = 0 := by
  rw [completedCreate, completedCreateMap, ContinuousLinearMap.comp_apply,
    completedSignedToggle_basisState, map_smul]
  simp [hi]

@[simp]
theorem completedCreate_basisState_of_not_mem {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    completedCreate i (completedBasisState n) =
      fermionPhase i n • completedBasisState (insertOccupation i n) := by
  rw [completedCreate, completedCreateMap, ContinuousLinearMap.comp_apply,
    completedSignedToggle_basisState, map_smul]
  simp [hi, toggleOccupation_of_not_mem]

@[simp]
theorem completedAnnihilate_basisState_of_not_mem {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    completedAnnihilate i (completedBasisState n) = 0 := by
  rw [completedAnnihilate, completedAnnihilateMap, ContinuousLinearMap.comp_apply,
    completedSignedToggle_basisState, map_smul]
  simp [hi]

@[simp]
theorem completedAnnihilate_basisState_of_mem {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    completedAnnihilate i (completedBasisState n) =
      fermionPhase i n • completedBasisState (removeOccupation i n) := by
  rw [completedAnnihilate, completedAnnihilateMap, ContinuousLinearMap.comp_apply,
    completedSignedToggle_basisState, map_smul]
  simp [hi, toggleOccupation_of_mem]

end
end Fermionic
end SecondQuantization
