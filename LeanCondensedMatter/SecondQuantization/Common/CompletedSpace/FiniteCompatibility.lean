import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteHilbertOperator
import Mathlib.Analysis.Normed.Lp.LpEquiv

set_option linter.style.header false

/-!
# Finite-configuration compatibility of completed Fock space

For a finite configuration type, the completed representation `ℓ²(Config, ℂ)` is canonically
linearly isometric to the finite Hilbert realization `EuclideanSpace ℂ Config`.

This construction depends only on the configuration basis, not on particle statistics. It preserves
coordinates, sends the completed basis to the finite Hilbert basis, and intertwines the canonical
algebraic embeddings.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- For finite configuration types, completed Fock space is canonically linearly isometric to the
finite Hilbert realization on the same configurations. -/
noncomputable def completedFiniteHilbertEquiv :
    CompletedFock Config ≃ₗᵢ[ℂ] FiniteHilbertFock Config :=
  lpPiLpₗᵢ (fun _ : Config => ℂ) ℂ

/-- Continuous-linear form of the canonical finite-configuration Hilbert-space equivalence. -/
noncomputable def completedFiniteHilbertContinuousEquiv :
    CompletedFock Config ≃L[ℂ] FiniteHilbertFock Config :=
  (completedFiniteHilbertEquiv (Config := Config)).toContinuousLinearEquiv

/-- The finite compatibility equivalence intertwines the algebraic-to-completed inclusion with the
algebraic-to-finite-Hilbert equivalence. -/
@[simp]
theorem completedFiniteHilbertEquiv_algebraicToCompleted
    (x : AlgebraicFock Config) :
    completedFiniteHilbertEquiv (Config := Config) (algebraicToCompleted x) =
      finiteHilbertFockEquiv x := by
  ext c
  rfl

/-- The completed configuration basis is exactly the finite Hilbert basis after transport through
the canonical finite compatibility equivalence. -/
@[simp]
theorem completedFiniteHilbertEquiv_basisState (c : Config) :
    completedFiniteHilbertEquiv (Config := Config) (completedBasisState c) =
      finiteHilbertBasisState c := by
  rw [← algebraicToCompleted_basisState,
    completedFiniteHilbertEquiv_algebraicToCompleted]
  exact finiteHilbertFockEquiv_basisState c

end
end Common
end SecondQuantization
