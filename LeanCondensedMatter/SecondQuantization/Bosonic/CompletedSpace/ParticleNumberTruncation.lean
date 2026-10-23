import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.CoordinateProjection

set_option linter.style.header false

/-!
# Bosonic completed-Fock particle-number truncation

The projection onto the subspace with total occupation at most `N` is contractive and
converges strongly to the identity as `N → ∞`. This is a particle-number cutoff,
not a finite-mode cutoff: if the mode type is infinite, the retained subspace
need not have finite dimension.
-/

namespace SecondQuantization
namespace Bosonic

open Filter Topology

noncomputable section

variable {Mode : Type*}

/-- Bounded coordinate projection onto bosonic configurations of particle number at most `N`. -/
noncomputable def completedParticleNumberTruncation (N : ℕ) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  Common.completedCoordinateProjection (fun n : Occupation Mode => particleNumber n ≤ N)

@[simp]
theorem completedParticleNumberTruncation_apply (N : ℕ)
    (ψ : CompletedFockSpace Mode) (n : Occupation Mode) :
    completedParticleNumberTruncation N ψ n =
      if particleNumber n ≤ N then ψ n else 0 := by
  classical
  simpa only [completedParticleNumberTruncation] using
    (Common.completedCoordinateProjection_apply
      (fun m : Occupation Mode => particleNumber m ≤ N) ψ n)

/-- Particle-number cutoffs converge strongly on completed bosonic Fock space, for arbitrary
mode types and without an assumption that the cutoff is finite rank. -/
theorem tendsto_completedParticleNumberTruncation (ψ : CompletedFockSpace Mode) :
    Tendsto (fun N : ℕ => completedParticleNumberTruncation N ψ) atTop (𝓝 ψ) := by
  change Tendsto (fun N : ℕ =>
    Common.completedCoordinateProjection
      (fun n : Occupation Mode => particleNumber n ≤ N) ψ) atTop (𝓝 ψ)
  exact Common.tendsto_completedCoordinateProjection_of_eventually atTop
    (fun N (n : Occupation Mode) => particleNumber n ≤ N)
    (fun n => eventually_ge_atTop (particleNumber n)) ψ

end
end Bosonic
end SecondQuantization
