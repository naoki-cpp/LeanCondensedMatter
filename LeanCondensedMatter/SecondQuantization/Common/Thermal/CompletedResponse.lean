import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.DiagonalAnalytic
import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolution
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation.Density
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Stationarity
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.DensitySusceptibility
import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.Integrability

set_option linter.style.header false

/-!
# Stationarity and adiabatic response of completed occupation-space Gibbs states

For bounded observables and a positive switching rate, the scalar response kernel is integrable
under real diagonal Stone dynamics. Strong continuity and summable Gibbs weights supply the
measurability hypothesis of the existing frequency-response theorem. Neither a finite-mode
assumption nor operator-norm continuity of observable orbits is imposed.

The same summable Gibbs state is stationary under these diagonal dynamics. Physical Hamiltonian
energies divided by ℏ may be used independently of the thermal generator `E - μ N`. The
integrability result concerns positive switching rate, not its zero-rate limit, unbounded observables,
or the existence of an infinite-volume state. Models supply the physically scaled generator `D`
and a positive value of `hbar`; the analytic statement itself does not need that positivity.
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

/-- A summable completed grand-canonical Gibbs state has an integrable adiabatic scalar response
for bounded observables at every positive switching rate under real diagonal Stone dynamics. -/
theorem adiabaticIntegrable_grandCanonicalGibbsDensityOperator
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable (grandCanonicalEnergy (Config := Config) ε μ) β)
    (D : Config → ℝ) (hbar : ℝ) (A B : CompletedFock Config →L[ℂ] CompletedFock Config)
    (ω η : ℝ) (hη : 0 < η) :
    AdiabaticIntegrable
      (LinearPMap.stoneEvolutionUnitaryGroup
        (completedDiagonalOperator (fun n => (D n : ℂ)))
        (completedDiagonalOperator_isSelfAdjoint_of_star _ (fun n => by simp)))
      hbar (grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum).toNormalizedExpectation
      A B ω η := by
  apply adiabaticIntegrable_of_pos _ _ _ A B ω η hη
  apply measurable_retardedTimeDifferenceKernel
  apply Continuous.measurable
  apply continuous_commutatorSusceptibility_of_diagonal_density _ _ _
    (completedHilbertBasis (Config := Config))
    (eigenbasisGibbsProbability (grandCanonicalEnergy (Config := Config) ε μ) β)
  · intro n
    simpa only [completedHilbertBasis_apply] using
      grandCanonicalGibbsDensityOperator_apply_basis ε β μ hsum n
  · intro x
    exact LinearPMap.stoneEvolution_apply_continuous _ _ x

end

end SecondQuantization.Common
