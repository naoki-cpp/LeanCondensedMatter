import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core

set_option linter.style.header false

/-!
# Canonical anticommutation relations on completed fermionic Fock space

The completed creation and annihilation operators are bounded continuous linear maps. This file
lifts the algebraic canonical anticommutation relations to the `ℓ²` completion. Rather than repeat
the occupation-coordinate sign calculation, the proof uses agreement with the algebraic ladder
operators on the finite-support core together with density of that core and continuity.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

omit [LinearOrder Mode] in
/-- The anticommutator of two bounded operators on completed fermionic Fock space. -/
noncomputable def completedAnticomm
    (A B : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  A.comp B + B.comp A

omit [LinearOrder Mode] in
@[simp]
theorem completedAnticomm_apply
    (A B : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode)
    (ψ : CompletedFockSpace Mode) :
    completedAnticomm A B ψ = A (B ψ) + B (A ψ) :=
  rfl

omit [LinearOrder Mode] in
/-- Continuous linear maps on completed Fock space are determined by their values on the dense
finite-support algebraic core. -/
private theorem continuousLinearMap_ext_algebraicCore
    {A B : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode}
    (h : ∀ x : OccupationFock Mode, A (algebraicToCompleted x) = B (algebraicToCompleted x)) :
    A = B := by
  apply DFunLike.ext'
  exact (map_continuous A).ext_on algebraicToCompleted_denseRange (map_continuous B) <| by
    rintro _ ⟨x, rfl⟩
    exact h x

private theorem completedCreate_algebraicToCompleted (i : Mode) (x : OccupationFock Mode) :
    completedCreate i (algebraicToCompleted x) = algebraicToCompleted (create i x) := by
  change (completedCreate i).toLinearMap (algebraicToCompleted x) =
    algebraicToCompleted (create i x)
  simpa only [LinearMap.comp_apply] using
    congrArg (fun f : OccupationFock Mode →ₗ[ℂ] CompletedFockSpace Mode => f x)
      (completedCreate_comp_algebraicToCompleted i)

private theorem completedAnnihilate_algebraicToCompleted (i : Mode) (x : OccupationFock Mode) :
    completedAnnihilate i (algebraicToCompleted x) = algebraicToCompleted (annihilate i x) := by
  change (completedAnnihilate i).toLinearMap (algebraicToCompleted x) =
    algebraicToCompleted (annihilate i x)
  simpa only [LinearMap.comp_apply] using
    congrArg (fun f : OccupationFock Mode →ₗ[ℂ] CompletedFockSpace Mode => f x)
      (completedAnnihilate_comp_algebraicToCompleted i)

/-- Completed creation operators anticommute. -/
theorem completedAnticomm_create_create (i j : Mode) :
    completedAnticomm (completedCreate i) (completedCreate j) = 0 := by
  apply continuousLinearMap_ext_algebraicCore
  intro x
  rw [completedAnticomm_apply]
  rw [completedCreate_algebraicToCompleted j x,
    completedCreate_algebraicToCompleted i (create j x),
    completedCreate_algebraicToCompleted i x,
    completedCreate_algebraicToCompleted j (create i x), ← map_add]
  have hcar : create i (create j x) + create j (create i x) = 0 := by
    have h := congrArg (fun f : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode => f x)
      (anticomm_create_create i j)
    simpa [anticomm_apply] using h
  rw [hcar, map_zero]
  rfl

/-- Completed annihilation operators anticommute. -/
theorem completedAnticomm_annihilate_annihilate (i j : Mode) :
    completedAnticomm (completedAnnihilate i) (completedAnnihilate j) = 0 := by
  apply continuousLinearMap_ext_algebraicCore
  intro x
  rw [completedAnticomm_apply]
  rw [completedAnnihilate_algebraicToCompleted j x,
    completedAnnihilate_algebraicToCompleted i (annihilate j x),
    completedAnnihilate_algebraicToCompleted i x,
    completedAnnihilate_algebraicToCompleted j (annihilate i x), ← map_add]
  have hcar : annihilate i (annihilate j x) + annihilate j (annihilate i x) = 0 := by
    have h := congrArg (fun f : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode => f x)
      (anticomm_annihilate_annihilate i j)
    simpa [anticomm_apply] using h
  rw [hcar, map_zero]
  rfl

/-- The mixed completed CAR: `{aᵢ, aⱼ†} = δᵢⱼ I`. -/
theorem completedAnticomm_annihilate_create (i j : Mode) :
    completedAnticomm (completedAnnihilate i) (completedCreate j) =
      if i = j then ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) else 0 := by
  apply continuousLinearMap_ext_algebraicCore
  intro x
  rw [completedAnticomm_apply]
  rw [completedCreate_algebraicToCompleted j x,
    completedAnnihilate_algebraicToCompleted i (create j x),
    completedAnnihilate_algebraicToCompleted i x,
    completedCreate_algebraicToCompleted j (annihilate i x), ← map_add]
  have hcar :
      annihilate i (create j x) + create j (annihilate i x) = if i = j then x else 0 := by
    have h := congrArg (fun f : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode => f x)
      (anticomm_annihilate_create i j)
    by_cases hij : i = j
    · simpa [anticomm_apply, hij] using h
    · simpa [anticomm_apply, hij] using h
  rw [hcar]
  by_cases hij : i = j <;> simp [hij]

omit [LinearOrder Mode] in
/-- The completed anticommutator is symmetric. -/
theorem completedAnticomm_comm
    (A B : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    completedAnticomm A B = completedAnticomm B A := by
  rw [completedAnticomm, completedAnticomm, add_comm]

/-- Creation-first form of the mixed completed CAR. -/
theorem completedAnticomm_create_annihilate (i j : Mode) :
    completedAnticomm (completedCreate i) (completedAnnihilate j) =
      if i = j then ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) else 0 := by
  rw [completedAnticomm_comm, completedAnticomm_annihilate_create]
  simp only [eq_comm]

end
end Fermionic
end SecondQuantization
