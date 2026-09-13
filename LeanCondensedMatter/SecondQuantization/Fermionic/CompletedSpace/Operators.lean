import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.CoordinateIsometry

set_option linter.style.header false

/-!
# Bounded operators on completed fermionic Fock space

This file specializes the statistics-independent completed-space coordinate isometries to fermionic
occupation toggles and signs, then uses them to construct the bounded creation and annihilation
operators. Both ladder maps are a unit-modulus fermionic phase times the occupation toggle,
restricted to the appropriate output sector.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

/-- The fermionic sign, regarded as a complex phase for completed-space operators. -/
def fermionPhase (i : Mode) (n : Occupation Mode) : ℂ :=
  fermionSign i n

@[simp]
theorem norm_fermionPhase (i : Mode) (n : Occupation Mode) :
    ‖fermionPhase i n‖ = 1 := by
  simp [fermionPhase, fermionSign]

/-- Reindex completed occupation amplitudes by toggling mode `i`. -/
noncomputable def completedToggle (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  (Common.completedReindex (toggleOccupationEquiv i)).toContinuousLinearMap

@[simp]
theorem completedToggle_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedToggle i ψ n = ψ (toggleOccupation i n) := by
  simpa [completedToggle, toggleOccupationEquiv_apply] using
    (Common.completedReindex_apply (toggleOccupationEquiv i) ψ n)

@[simp]
theorem completedToggle_completedToggle (i : Mode) (ψ : CompletedFockSpace Mode) :
    completedToggle i (completedToggle i ψ) = ψ := by
  ext n
  rw [completedToggle_apply, completedToggle_apply, toggleOccupation_involutive i n]

private noncomputable def completedSignedToggle (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  (Common.completedPhaseMultiplier
      (fun n : Occupation Mode => fermionPhase i (toggleOccupation i n))
      (fun n => norm_fermionPhase i (toggleOccupation i n))).toContinuousLinearMap.comp
    (completedToggle i)

@[simp]
private theorem completedSignedToggle_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedSignedToggle i ψ n =
      fermionPhase i (toggleOccupation i n) * ψ (toggleOccupation i n) := by
  simp [completedSignedToggle, completedToggle, toggleOccupationEquiv_apply]

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
  simp [completedSignedToggle, completedToggle, completedBasisState,
    toggleOccupationEquiv_symm, toggleOccupationEquiv_apply, toggleOccupation_involutive]

@[simp]
theorem completedCreate_basisState_of_mem {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    completedCreate i (completedBasisState n) = 0 := by
  rw [completedCreate, completedCreateMap, ContinuousLinearMap.comp_apply,
    completedSignedToggle_basisState, map_smul]
  change fermionPhase i n •
      Common.completedCoordinateProjection (fun m : Occupation Mode => i ∈ m)
        (Common.completedBasisState (toggleOccupation i n)) = 0
  rw [Common.completedCoordinateProjection_basisState]
  simp [hi, removeOccupation]

@[simp]
theorem completedCreate_basisState_of_not_mem {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    completedCreate i (completedBasisState n) =
      fermionPhase i n • completedBasisState (insertOccupation i n) := by
  rw [completedCreate, completedCreateMap, ContinuousLinearMap.comp_apply,
    completedSignedToggle_basisState, map_smul]
  change fermionPhase i n •
      Common.completedCoordinateProjection (fun m : Occupation Mode => i ∈ m)
        (Common.completedBasisState (toggleOccupation i n)) =
    fermionPhase i n • Common.completedBasisState (insertOccupation i n)
  rw [Common.completedCoordinateProjection_basisState]
  simp [hi, insertOccupation]

@[simp]
theorem completedAnnihilate_basisState_of_not_mem {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    completedAnnihilate i (completedBasisState n) = 0 := by
  rw [completedAnnihilate, completedAnnihilateMap, ContinuousLinearMap.comp_apply,
    completedSignedToggle_basisState, map_smul]
  change fermionPhase i n •
      Common.completedCoordinateProjection (fun m : Occupation Mode => i ∉ m)
        (Common.completedBasisState (toggleOccupation i n)) = 0
  rw [Common.completedCoordinateProjection_basisState]
  simp [hi, insertOccupation]

@[simp]
theorem completedAnnihilate_basisState_of_mem {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    completedAnnihilate i (completedBasisState n) =
      fermionPhase i n • completedBasisState (removeOccupation i n) := by
  rw [completedAnnihilate, completedAnnihilateMap, ContinuousLinearMap.comp_apply,
    completedSignedToggle_basisState, map_smul]
  change fermionPhase i n •
      Common.completedCoordinateProjection (fun m : Occupation Mode => i ∉ m)
        (Common.completedBasisState (toggleOccupation i n)) =
    fermionPhase i n • Common.completedBasisState (removeOccupation i n)
  rw [Common.completedCoordinateProjection_basisState]
  simp [hi, removeOccupation]

end
end Fermionic
end SecondQuantization
