import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteAnalyticBridge
import LeanCondensedMatter.QuantumTheory.DiagonalDensityLemmasTraceClass

set_option linter.style.header false

/-!
# Finite-configuration Gibbs density operators

A finite occupation/configuration basis carries a canonical Euclidean Hilbert-space realization.
Positive Boltzmann weights on that basis therefore define a genuine trace-class density operator,
not merely a normalized coordinate functional.
-/

namespace SecondQuantization
namespace Common

noncomputable section

open QuantumTheory.TraceClass

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The canonical coordinate orthonormal basis of the finite analytic Fock space. -/
noncomputable def finiteAnalyticOrthonormalBasis :
    OrthonormalBasis Config ℂ (FiniteAnalyticFock Config) :=
  EuclideanSpace.basisFun Config ℂ

/-- The canonical coordinate Hilbert basis of the finite analytic Fock space. -/
noncomputable def finiteAnalyticHilbertBasis :
    HilbertBasis Config ℂ (FiniteAnalyticFock Config) :=
  (finiteAnalyticOrthonormalBasis (Config := Config)).toHilbertBasis

@[simp]
theorem finiteAnalyticOrthonormalBasis_apply (n : Config) :
    finiteAnalyticOrthonormalBasis (Config := Config) n = finiteAnalyticBasis n :=
  rfl

@[simp]
theorem finiteAnalyticHilbertBasis_apply (n : Config) :
    finiteAnalyticHilbertBasis (Config := Config) n = finiteAnalyticBasis n :=
  rfl

/-- The positive real Boltzmann weight `exp (-β E(n))`. -/
noncomputable def finiteBoltzmannWeight (energy : Config → ℝ) (β : ℝ) (n : Config) : ℝ :=
  Real.exp (-β * energy n)

/-- The real finite partition function. -/
noncomputable def finitePartitionFunction (energy : Config → ℝ) (β : ℝ) : ℝ :=
  ∑' n : Config, finiteBoltzmannWeight energy β n

/-- The finite Boltzmann family has its defining finite sum. -/
theorem hasSum_finiteBoltzmannWeight (energy : Config → ℝ) (β : ℝ) :
    HasSum (finiteBoltzmannWeight energy β) (finitePartitionFunction energy β) := by
  rw [finitePartitionFunction]
  exact hasSum_fintype _

/-- The finite partition function is strictly positive. -/
theorem finitePartitionFunction_pos (energy : Config → ℝ) (β : ℝ) :
    0 < finitePartitionFunction energy β := by
  rw [finitePartitionFunction, tsum_fintype]
  exact Finset.sum_pos (fun n _ => Real.exp_pos _) Finset.univ_nonempty

/-- The canonical finite Gibbs state as a trace-class density operator. -/
noncomputable def finiteGibbsDensityOperator (energy : Config → ℝ) (β : ℝ) :
    QuantumTheory.TraceClass.DensityOperator (FiniteAnalyticFock Config) :=
  diagonalDensityOperator
    (finiteAnalyticHilbertBasis (Config := Config))
    (finiteBoltzmannWeight energy β)
    Summable.of_finite
    (fun n => (Real.exp_pos _).le)
    (finitePartitionFunction_pos energy β)

/-- The finite Gibbs density operator acts diagonally with normalized Boltzmann weights. -/
@[simp]
theorem finiteGibbsDensityOperator_apply_basis (energy : Config → ℝ) (β : ℝ) (n : Config) :
    (finiteGibbsDensityOperator energy β).op (finiteAnalyticBasis n) =
      (((finitePartitionFunction energy β)⁻¹ * finiteBoltzmannWeight energy β n : ℝ) : ℂ) •
        finiteAnalyticBasis n := by
  simpa [finiteGibbsDensityOperator, finitePartitionFunction, normalizedDiagonalWeight] using
    diagonalDensityOperator_apply_basis
      (finiteAnalyticHilbertBasis (Config := Config))
      (finiteBoltzmannWeight energy β)
      (Summable.of_finite : Summable fun n : Config => ‖finiteBoltzmannWeight energy β n‖)
      (fun n => (Real.exp_pos _).le)
      (finitePartitionFunction_pos energy β) n

end
end Common
end SecondQuantization
