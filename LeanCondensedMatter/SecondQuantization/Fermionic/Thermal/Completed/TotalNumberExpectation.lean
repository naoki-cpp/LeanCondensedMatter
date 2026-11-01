import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.Gibbs
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonicalSectorDecomposition
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal

set_option linter.style.header false

/-!
# Completed free-fermion grand-canonical total-number expectation

The completed total-number operator is genuinely unbounded, so it is not passed to
`DensityOperator.expectation`, whose observable argument is bounded. Instead its Gibbs expectation
is the spectral series of its occupation-basis eigenvalues. Absolute convergence is tracked by an
explicit total-number integrability condition; existence of the completed free Gibbs density state
is required only by the bridge back to the density operator.

The operator and its maximal domain remain owned by `Fermionic.CompletedSpace.Diagonal`. This module
relates their completed Gibbs matrix elements to the common particle-number spectral expectation,
using the common grand-canonical integrability condition. Generic pure-point energy expectations
remain in `QuantumTheory.Gibbs.EigenbasisExpectation`.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- The diagonal matrix elements of the actual completed Gibbs density operator composed with the
completed total-number operator sum to the real spectral expectation. -/
theorem hasSum_grandCanonicalGibbsDensityOperator_totalNumber_diagonal
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (hint : Common.GrandCanonicalParticleNumberIntegrable (Config := Occupation Mode) ε β μ) :
    HasSum
      (fun n : Occupation Mode =>
        inner ℂ (completedBasisState n)
          ((Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op
            (completedTotalNumberOperator
              ⟨completedBasisState n, completedBasisState_mem_completedTotalNumberDomain n⟩)))
      (Common.grandCanonicalParticleNumberExpectation (Config := Occupation Mode) ε β μ : ℂ) := by
  have hcast :=
    (Common.hasSum_grandCanonicalParticleNumberExpectation
      (Config := Occupation Mode) ε β μ hint).mapL Complex.ofRealCLM
  simp only [Complex.ofRealCLM_apply] at hcast
  exact HasSum.congr_fun hcast fun n => by
    symm
    have hnorm : ‖completedBasisState n‖ = 1 := by
      rw [← completedOccupationHilbertBasis_apply]
      exact (completedOccupationHilbertBasis (Mode := Mode)).orthonormal.norm_eq_one n
    rw [completedTotalNumberOperator_basisState, map_smul]
    simp only [completedBasisState] at hnorm ⊢
    rw [Common.grandCanonicalGibbsDensityOperator_apply_basis,
      inner_smul_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
    ring

end
end Fermionic
end SecondQuantization
