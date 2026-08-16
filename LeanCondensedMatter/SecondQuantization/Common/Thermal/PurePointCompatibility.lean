import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsDensityOperator
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

set_option linter.style.header false

/-!
# Compatibility with the generic pure-point Gibbs state

The finite configuration-space Gibbs state is exactly the finite specialization of the generic
pure-point Gibbs construction.  This module keeps that bridge downstream in `SecondQuantization`,
so the generic `QuantumTheory` layer remains independent of occupation-basis infrastructure.
-/

namespace SecondQuantization
namespace Common

noncomputable section

open QuantumTheory

variable {Config : Type*}

@[simp]
theorem finiteBoltzmannWeight_eq_purePointBoltzmannWeight
    (energy : Config → ℝ) (β : ℝ) (n : Config) :
    finiteBoltzmannWeight energy β n = purePointBoltzmannWeight energy β n :=
  rfl

@[simp]
theorem finitePartitionFunction_eq_purePointPartitionFunction
    (energy : Config → ℝ) (β : ℝ) :
    finitePartitionFunction energy β = purePointPartitionFunction energy β :=
  rfl

variable [Fintype Config] [Nonempty Config]

/-- The canonical finite-configuration Gibbs density operator is definitionally the finite
specialization of the generic pure-point Gibbs density operator on the same Hilbert basis. -/
theorem finiteGibbsDensityOperator_eq_finitePurePointGibbsDensityOperator
    (energy : Config → ℝ) (β : ℝ) :
    finiteGibbsDensityOperator energy β =
      finitePurePointGibbsDensityOperator
        (finiteHilbertBasis (Config := Config)) energy β := by
  rfl

/-- The finite Gibbs density operator therefore acts with the generic pure-point probabilities. -/
theorem finiteGibbsDensityOperator_apply_basis_eq_purePointProbability
    (energy : Config → ℝ) (β : ℝ) (n : Config) :
    (finiteGibbsDensityOperator energy β).op (finiteHilbertBasisState n) =
      (purePointGibbsProbability energy β n : ℂ) • finiteHilbertBasisState n := by
  rw [finiteGibbsDensityOperator_eq_finitePurePointGibbsDensityOperator]
  simpa using finitePurePointGibbsDensityOperator_apply_basis
    (finiteHilbertBasis (Config := Config)) energy β n

end
end Common
end SecondQuantization
