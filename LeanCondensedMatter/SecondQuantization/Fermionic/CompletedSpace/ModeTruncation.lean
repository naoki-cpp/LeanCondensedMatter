import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.CoordinateProjection

set_option linter.style.header false

/-!
# Finite-mode truncations of completed fermionic Fock space

For a finite set of modes `S`, `completedModeTruncation S` keeps exactly those occupation
configurations contained in `S`.  It is a contractive coordinate projection.  As `S` increases in
the directed set `Finset Mode` ordered by inclusion, these projections converge strongly to the
identity on completed fermionic Fock space.

The coordinate-mask implementation and generic strong convergence are owned by `Common.CompletedSpace`;
this file specializes the result to fermionic finite-mode occupations.

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

/-- Finite-mode truncations converge strongly to the identity as the finite mode set increases.
This is a net convergence theorem over `Finset Mode`, not a sequential statement. -/
theorem tendsto_completedModeTruncation (ψ : CompletedFockSpace Mode) :
    Tendsto (fun S : Finset Mode => completedModeTruncation S ψ) atTop (𝓝 ψ) := by
  change Tendsto (fun S : Finset Mode =>
    Common.completedCoordinateProjection (fun n : Occupation Mode => n ⊆ S) ψ)
      atTop (𝓝 ψ)
  exact Common.tendsto_completedCoordinateProjection_of_eventually atTop
    (fun S (n : Occupation Mode) => n ⊆ S)
    (fun n => eventually_ge_atTop n) ψ

end
end Fermionic
end SecondQuantization
