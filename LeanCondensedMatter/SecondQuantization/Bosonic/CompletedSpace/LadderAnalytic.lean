import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Ladder
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.DiagonalAnalytic
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option linter.style.header false

/-!
# Analytic properties of completed bosonic ladder operators

The completed creation and annihilation operators are densely defined mutual adjoints on their
maximal weighted-shift domains. Consequently both operators are closed.

The proof factors the shift through the statistics-independent injective coordinate embedding and
its bounded Hilbert-space adjoint. The remaining unbounded factor is the real diagonal square-root
occupation weight handled by the Common diagonal analytic theory.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- The completed creation operator is densely defined. -/
theorem completedCreate_denseDomain (i : Mode) :
    Dense (((completedCreate i).domain : Submodule ℂ (CompletedFockSpace Mode)) :
      Set (CompletedFockSpace Mode)) := by
  change Dense ((completedCreateDomain i : Submodule ℂ (CompletedFockSpace Mode)) :
    Set (CompletedFockSpace Mode))
  exact Common.completedDiagonalOperator_denseDomain
    (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ))

/-- The completed annihilation operator is densely defined. -/
theorem completedAnnihilate_denseDomain (i : Mode) :
    Dense (((completedAnnihilate i).domain : Submodule ℂ (CompletedFockSpace Mode)) :
      Set (CompletedFockSpace Mode)) := by
  change Dense ((completedAnnihilateDomain i : Submodule ℂ (CompletedFockSpace Mode)) :
    Set (CompletedFockSpace Mode))
  exact Common.completedDiagonalOperator_denseDomain
    (fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ))

private theorem completedCoordinatePullback_mem_completedCreateDomain
    (i : Mode) (y : (completedAnnihilate i).domain) :
    Common.completedCoordinatePullback
        (createOccupation i) (createOccupation_injective i)
        (y : CompletedFockSpace Mode) ∈
      completedCreateDomain i := by
  rw [Common.mem_completedDiagonalDomain_iff]
  have hmem :=
    lp.memℓp
      (Common.completedCoordinatePullback
        (createOccupation i) (createOccupation_injective i)
        (Common.completedDiagonalOperator
          (fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ)) y))
  convert hmem using 1
  funext n
  rw [Common.completedCoordinatePullback_apply]
  rw [Common.completedCoordinatePullback_apply]
  change
    (Real.sqrt (n i + 1 : ℝ) : ℂ) *
        (y : CompletedFockSpace Mode) (createOccupation i n) =
      (Real.sqrt ((createOccupation i n) i : ℝ) : ℂ) *
        (y : CompletedFockSpace Mode) (createOccupation i n)
  rw [createOccupation_apply_same, Nat.cast_add, Nat.cast_one]

private theorem completedCreateDiagonal_pullback_eq
    (i : Mode) (y : (completedAnnihilate i).domain) :
    Common.completedDiagonalOperator
        (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ))
        ⟨Common.completedCoordinatePullback
            (createOccupation i) (createOccupation_injective i)
            (y : CompletedFockSpace Mode),
          completedCoordinatePullback_mem_completedCreateDomain i y⟩ =
      Common.completedCoordinatePullback
        (createOccupation i) (createOccupation_injective i)
        (Common.completedDiagonalOperator
          (fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ)) y) := by
  ext n
  rw [Common.completedDiagonalOperator_apply,
    Common.completedCoordinatePullback_apply]
  rw [Common.completedCoordinatePullback_apply]
  change
    (Real.sqrt (n i + 1 : ℝ) : ℂ) *
        (y : CompletedFockSpace Mode) (createOccupation i n) =
      (Real.sqrt ((createOccupation i n) i : ℝ) : ℂ) *
        (y : CompletedFockSpace Mode) (createOccupation i n)
  rw [createOccupation_apply_same, Nat.cast_add, Nat.cast_one]

/-- Completed creation and annihilation are formal adjoints on their maximal weighted domains. -/
theorem completedCreate_isFormalAdjoint_completedAnnihilate (i : Mode) :
    (completedCreate i).IsFormalAdjoint (completedAnnihilate i) := by
  intro x y
  let py :
      (Common.completedDiagonalOperator
        (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ))).domain :=
    ⟨Common.completedCoordinatePullback
        (createOccupation i) (createOccupation_injective i)
        (y : CompletedFockSpace Mode),
      completedCoordinatePullback_mem_completedCreateDomain i y⟩
  have hdiag :=
    Common.completedDiagonalOperator_isFormalAdjoint_self
      (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ))
      (fun n => by simp) x py
  calc
    inner ℂ (completedCreate i x) (y : CompletedFockSpace Mode) =
        inner ℂ
          (Common.completedDiagonalOperator
            (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ)) x)
          (Common.completedCoordinatePullback
            (createOccupation i) (createOccupation_injective i)
            (y : CompletedFockSpace Mode)) := by
      change
        inner ℂ
          ((Common.completedCoordinateEmbedding
            (createOccupation i) (createOccupation_injective i)).toContinuousLinearMap
            (Common.completedDiagonalOperator
              (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ)) x))
          (y : CompletedFockSpace Mode) = _
      rw [← ContinuousLinearMap.adjoint_inner_right]
      rfl
    _ = inner ℂ (x : CompletedFockSpace Mode)
        (Common.completedDiagonalOperator
          (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ)) py) := hdiag
    _ = inner ℂ (x : CompletedFockSpace Mode) (completedAnnihilate i y) := by
      rw [completedCreateDiagonal_pullback_eq]
      rfl

/-- Completed annihilation is the reverse formal adjoint of completed creation. -/
theorem completedAnnihilate_isFormalAdjoint_completedCreate (i : Mode) :
    (completedAnnihilate i).IsFormalAdjoint (completedCreate i) :=
  (completedCreate_isFormalAdjoint_completedAnnihilate i).symm

private theorem completedCreate_adjoint_apply
    (i : Mode) (y : (completedCreate i).adjoint.domain) (n : Occupation Mode) :
    (completedCreate i).adjoint y n =
      (Real.sqrt (n i + 1 : ℝ) : ℂ) *
        (y : CompletedFockSpace Mode) (createOccupation i n) := by
  let e : (completedCreate i).domain :=
    ⟨completedBasisState n, completedBasisState_mem_completedCreateDomain i n⟩
  have h :=
    ((completedCreate i).adjoint_isFormalAdjoint
      (completedCreate_denseDomain i)).symm e y
  have he :
      completedCreate i e =
        (Real.sqrt (n i + 1 : ℝ) : ℂ) •
          completedBasisState (createOccupation i n) := by
    exact completedCreate_basisState i n _
  rw [he] at h
  simpa [inner_smul_left] using h.symm

private theorem completedCreate_adjoint_domain_le_annihilateDomain (i : Mode) :
    (completedCreate i).adjoint.domain ≤ completedAnnihilateDomain i := by
  intro y hy
  rw [Common.mem_completedDiagonalDomain_iff]
  let yAdj : (completedCreate i).adjoint.domain := ⟨y, hy⟩
  have hmem :=
    lp.memℓp
      (Common.completedCoordinateEmbedding
        (createOccupation i) (createOccupation_injective i)
        ((completedCreate i).adjoint yAdj))
  convert hmem using 1
  funext n
  rw [Common.completedCoordinateEmbedding_apply]
  by_cases hni : n i = 0
  · rw [hni]
    simp only [Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul]
    rw [Function.extend_apply']
    · rfl
    · intro h
      rcases h with ⟨m, hm⟩
      have hcoord := congrArg (fun q : Occupation Mode => q i) hm
      rw [createOccupation_apply_same, hni] at hcoord
      omega
  · have hrepr : createOccupation i (removeOccupation i n) = n :=
      createOccupation_removeOccupation_of_pos hni
    have hcoord : (removeOccupation i n) i + 1 = n i := by
      have h := congrArg (fun q : Occupation Mode => q i) hrepr
      simpa only [createOccupation_apply_same] using h
    have hcoord_real : ((removeOccupation i n) i : ℝ) + 1 = (n i : ℝ) := by
      exact_mod_cast hcoord
    conv_rhs => rw [← hrepr]
    rw [(createOccupation_injective i).extend_apply,
      completedCreate_adjoint_apply, hcoord_real, hrepr]

/-- The adjoint of completed creation is exactly completed annihilation. -/
theorem completedCreate_adjoint_eq_completedAnnihilate (i : Mode) :
    (completedCreate i).adjoint = completedAnnihilate i := by
  apply le_antisymm
  · refine ⟨completedCreate_adjoint_domain_le_annihilateDomain i, ?_⟩
    intro x y hxy
    ext n
    rw [completedCreate_adjoint_apply, completedAnnihilate_apply]
    change
      (Real.sqrt (n i + 1 : ℝ) : ℂ) *
          (x : CompletedFockSpace Mode) (createOccupation i n) =
        (Real.sqrt (n i + 1 : ℝ) : ℂ) *
          (y : CompletedFockSpace Mode) (createOccupation i n)
    rw [hxy]
  · exact
      (completedCreate_isFormalAdjoint_completedAnnihilate i).le_adjoint
        (completedCreate_denseDomain i)

private theorem completedAnnihilate_adjoint_apply
    (i : Mode) (y : (completedAnnihilate i).adjoint.domain) (n : Occupation Mode) :
    (completedAnnihilate i).adjoint y n =
      (Real.sqrt (n i : ℝ) : ℂ) *
        (y : CompletedFockSpace Mode) (removeOccupation i n) := by
  let e : (completedAnnihilate i).domain :=
    ⟨completedBasisState n, completedBasisState_mem_completedAnnihilateDomain i n⟩
  have h :=
    ((completedAnnihilate i).adjoint_isFormalAdjoint
      (completedAnnihilate_denseDomain i)).symm e y
  have he :
      completedAnnihilate i e =
        (Real.sqrt (n i : ℝ) : ℂ) •
          completedBasisState (removeOccupation i n) := by
    exact completedAnnihilate_basisState i n _
  rw [he] at h
  simpa [inner_smul_left] using h.symm

private theorem completedAnnihilate_adjoint_domain_le_createDomain (i : Mode) :
    (completedAnnihilate i).adjoint.domain ≤ completedCreateDomain i := by
  intro y hy
  rw [Common.mem_completedDiagonalDomain_iff]
  let yAdj : (completedAnnihilate i).adjoint.domain := ⟨y, hy⟩
  have hmem :=
    lp.memℓp
      (Common.completedCoordinatePullback
        (createOccupation i) (createOccupation_injective i)
        ((completedAnnihilate i).adjoint yAdj))
  convert hmem using 1
  funext n
  rw [Common.completedCoordinatePullback_apply,
    completedAnnihilate_adjoint_apply,
    createOccupation_apply_same,
    removeOccupation_createOccupation,
    Nat.cast_add, Nat.cast_one]

/-- The adjoint of completed annihilation is exactly completed creation. -/
theorem completedAnnihilate_adjoint_eq_completedCreate (i : Mode) :
    (completedAnnihilate i).adjoint = completedCreate i := by
  apply le_antisymm
  · refine ⟨completedAnnihilate_adjoint_domain_le_createDomain i, ?_⟩
    intro x y hxy
    ext n
    rw [completedAnnihilate_adjoint_apply, completedCreate_apply]
    by_cases hni : n i = 0
    · rw [ite_eq_left hni, hni]
      simp
    · rw [ite_eq_right hni]
      change
        (Real.sqrt (n i : ℝ) : ℂ) *
            (x : CompletedFockSpace Mode) (removeOccupation i n) =
          (Real.sqrt (n i : ℝ) : ℂ) *
            (y : CompletedFockSpace Mode) (removeOccupation i n)
      rw [hxy]
  · exact
      (completedAnnihilate_isFormalAdjoint_completedCreate i).le_adjoint
        (completedAnnihilate_denseDomain i)

/-- Completed bosonic creation is closed on its maximal weighted-shift domain. -/
theorem completedCreate_isClosed (i : Mode) :
    (completedCreate i).IsClosed := by
  rw [← completedAnnihilate_adjoint_eq_completedCreate i]
  exact LinearPMap.adjoint_isClosed (completedAnnihilate_denseDomain i)

/-- Completed bosonic annihilation is closed on its maximal weighted-shift domain. -/
theorem completedAnnihilate_isClosed (i : Mode) :
    (completedAnnihilate i).IsClosed := by
  rw [← completedCreate_adjoint_eq_completedAnnihilate i]
  exact LinearPMap.adjoint_isClosed (completedCreate_denseDomain i)

end
end Bosonic
end SecondQuantization
