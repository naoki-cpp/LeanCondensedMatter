import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic

set_option linter.style.header false

/-!
# Finite-mode truncations of completed fermionic Fock space

For a finite set of modes `S`, `completedModeTruncation S` keeps exactly those occupation
configurations contained in `S`.  It is a contractive coordinate projection.  As `S` increases in
the directed set `Finset Mode` ordered by inclusion, these projections converge strongly to the
identity on completed fermionic Fock space.

The coordinate-mask implementation and contractivity are owned by `Common.CompletedSpace`; this
file keeps the fermionic finite-support semantics and strong-convergence argument.

The convergence is formulated as a net rather than a sequence, so no countability assumption on the
ambient mode type is required.
-/

namespace SecondQuantization
namespace Fermionic

open Filter Topology

noncomputable section

variable {Mode : Type*}

/-- Classical decidable equality used internally by finite-mode truncation. -/
local instance completedModeTruncationDecidableEq : DecidableEq Mode := Classical.decEq Mode

/-- Finite-mode truncation as a bounded projection of norm at most one. -/
noncomputable def completedModeTruncation (S : Finset Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  Common.completedCoordinateProjection (fun n : Occupation Mode => n ⊆ S)

@[simp]
theorem completedModeTruncation_apply (S : Finset Mode)
    (ψ : CompletedFockSpace Mode) (n : Occupation Mode) :
    completedModeTruncation S ψ n = if n ⊆ S then ψ n else 0 := by
  simpa [completedModeTruncation] using
    (Common.completedCoordinateProjection_apply
      (Config := Occupation Mode) (fun m : Occupation Mode => m ⊆ S) ψ n)

/-- A basis state survives exactly when its occupation configuration is contained in `S`. -/
theorem completedModeTruncation_basisState (S : Finset Mode) (n : Occupation Mode) :
    completedModeTruncation S (completedBasisState n) =
      if n ⊆ S then completedBasisState n else 0 := by
  simpa [completedModeTruncation, completedBasisState] using
    (Common.completedCoordinateProjection_basisState
      (Config := Occupation Mode) (fun m : Occupation Mode => m ⊆ S) n)

/-- The finite set of ambient modes occurring in the support of an algebraic Fock vector. -/
noncomputable def algebraicModeSupport (x : OccupationFock Mode) : Finset Mode := by
  classical
  exact x.support.biUnion id

/-- Every occupation configuration carrying a nonzero algebraic coefficient is contained in the
finite ambient-mode support. -/
theorem occupation_subset_algebraicModeSupport (x : OccupationFock Mode) (n : Occupation Mode)
    (hn : x n ≠ 0) :
    n ⊆ algebraicModeSupport x := by
  classical
  intro i hi
  have hnsupp : n ∈ x.support := Finsupp.mem_support_iff.mpr hn
  simp only [algebraicModeSupport, Finset.mem_biUnion]
  exact ⟨n, hnsupp, hi⟩

/-- Once `S` contains every mode appearing in an algebraic vector, finite-mode truncation fixes its
completed image exactly. -/
theorem completedModeTruncation_algebraicToCompleted_of_subset
    (S : Finset Mode) (x : OccupationFock Mode)
    (hS : algebraicModeSupport x ⊆ S) :
    completedModeTruncation S (algebraicToCompleted x) = algebraicToCompleted x := by
  classical
  ext n
  rw [completedModeTruncation_apply]
  by_cases hn : x n = 0
  · simp [algebraicToCompleted_apply, hn]
  · have hnsub : n ⊆ S := (occupation_subset_algebraicModeSupport x n hn).trans hS
    simp [algebraicToCompleted_apply, hnsub]

/-- A contraction that fixes `φ` moves `ψ` by at most twice the distance from `ψ` to `φ`. -/
theorem dist_completedModeTruncation_le_two_mul_of_fixed
    (S : Finset Mode) (ψ φ : CompletedFockSpace Mode)
    (hφ : completedModeTruncation S φ = φ) :
    dist (completedModeTruncation S ψ) ψ ≤ 2 * dist ψ φ := by
  have hcontract :
      dist (completedModeTruncation S ψ) (completedModeTruncation S φ) ≤ dist ψ φ := by
    simpa [completedModeTruncation] using
      (Common.dist_completedCoordinateProjection_le
        (Config := Occupation Mode) (fun n : Occupation Mode => n ⊆ S) ψ φ)
  calc
    dist (completedModeTruncation S ψ) ψ ≤
        dist (completedModeTruncation S ψ) (completedModeTruncation S φ) +
          dist (completedModeTruncation S φ) ψ :=
      dist_triangle _ _ _
    _ = dist (completedModeTruncation S ψ) (completedModeTruncation S φ) + dist φ ψ := by
      rw [hφ]
    _ ≤ dist ψ φ + dist φ ψ := by
      exact add_le_add hcontract (le_refl _)
    _ = 2 * dist ψ φ := by
      rw [dist_comm φ ψ, two_mul]

private theorem eventually_dist_completedModeTruncation_lt
    (ψ : CompletedFockSpace Mode) {ε : ℝ} (hε : 0 < ε) :
    ∃ S₀ : Finset Mode, ∀ S, S₀ ⊆ S → dist (completedModeTruncation S ψ) ψ < ε := by
  have hhalf : 0 < ε / 2 := half_pos hε
  rcases algebraicToCompleted_denseRange.exists_dist_lt ψ hhalf with ⟨x, hx⟩
  refine ⟨algebraicModeSupport x, ?_⟩
  intro S hS
  have hfix := completedModeTruncation_algebraicToCompleted_of_subset S x hS
  calc
    dist (completedModeTruncation S ψ) ψ ≤ 2 * dist ψ (algebraicToCompleted x) :=
      dist_completedModeTruncation_le_two_mul_of_fixed S ψ (algebraicToCompleted x) hfix
    _ < ε := by linarith

/-- Finite-mode truncations converge strongly to the identity as the finite mode set increases.
This is a net convergence theorem over `Finset Mode`, not a sequential statement. -/
theorem tendsto_completedModeTruncation (ψ : CompletedFockSpace Mode) :
    Tendsto (fun S : Finset Mode => completedModeTruncation S ψ) atTop (𝓝 ψ) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  exact eventually_dist_completedModeTruncation_lt ψ hε

end
end Fermionic
end SecondQuantization
