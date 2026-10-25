import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.DiagonalAnalytic
import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolution
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation.Density
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Stationarity

set_option linter.style.header false

/-!
# Stationarity of occupation-diagonal Gibbs states

The existing full-Fock grand-canonical Gibbs state is invariant under Stone evolution of any
real energy function diagonal in the same occupation basis. In particular, physical dynamics may
use the Hamiltonian energies divided by ℏ; it need not use the grand-canonical energies `E - μ N`.
The Boltzmann summability hypothesis is retained, without a finite-mode assumption. This result
applies to both fermionic and bosonic occupation bases and bounded observables.
-/

namespace SecondQuantization.Common

open QuantumTheory QuantumTheory.LinearResponse

noncomputable section

variable {Mode Config : Type*} [OccupationBasis Mode Config]

/-- A summable occupation-diagonal Gibbs state is stationary under every real diagonal Stone
generator on that occupation space. `D` specifies the dynamical energies independently of `μ`. -/
theorem isStationary_grandCanonicalGibbsDensityOperator
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable (grandCanonicalEnergy (Config := Config) ε μ) β)
    (D : Config → ℝ) :
    IsStationary
      (LinearPMap.stoneEvolutionUnitaryGroup
        (completedDiagonalOperator (fun n => (D n : ℂ)))
        (completedDiagonalOperator_isSelfAdjoint_of_star _ (fun n => by simp)))
      (grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum).toNormalizedExpectation := by
  intro t B
  let ρ := grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum
  let p := eigenbasisGibbsProbability (grandCanonicalEnergy (Config := Config) ε μ) β
  have hρ (n : Config) : ρ.op (completedHilbertBasis n) =
      (p n : ℂ) • completedHilbertBasis n := by
    simpa only [completedHilbertBasis_apply] using
      grandCanonicalGibbsDensityOperator_apply_basis ε β μ hsum n
  change ρ.expectation _ = ρ.expectation B
  rw [ρ.expectation_eq_tsum_diagonal _ completedHilbertBasis p hρ,
    ρ.expectation_eq_tsum_diagonal _ completedHilbertBasis p hρ]
  apply tsum_congr
  intro n
  congr 1
  simp only [heisenbergEvolution_apply, LinearPMap.stoneEvolutionUnitaryGroup_apply,
    mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, completedHilbertBasis_apply]
  exact LinearPMap.inner_stoneEvolution_eigenvector _ _
    ⟨completedBasisState n, completedBasisState_mem_completedDiagonalDomain _ n⟩
    (D n) (completedDiagonalOperator_basisState _ n) B t

end

end SecondQuantization.Common
