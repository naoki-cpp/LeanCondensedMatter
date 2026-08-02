import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import LeanCondensedMatter.QuantumTheory.DiagonalDensityLemmasTraceClass
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false

/-!
# Finite-configuration Gibbs density operators

A finite occupation/configuration basis carries a canonical Euclidean Hilbert-space realization.
Positive Boltzmann weights on that basis therefore define a genuine trace-class density operator,
not merely a normalized coordinate functional.

This Hilbert realization is introduced separately from the existing finite analytic Dyson
realization, which currently uses the sup-norm function space. The destructive replacement of that
analytic representation is deferred until its operator-continuity proofs and all callers migrate in
one package; no compatibility alias between the two spaces is introduced here.
-/

namespace SecondQuantization
namespace Common

noncomputable section

open QuantumTheory.TraceClass

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The finite-dimensional Hilbert realization of the algebraic Fock basis. -/
abbrev FiniteHilbertFock (Config : Type*) := EuclideanSpace ℂ Config

/-- The standard occupation/configuration basis vector in the finite Hilbert Fock space. -/
noncomputable def finiteHilbertBasisState (n : Config) : FiniteHilbertFock Config :=
  EuclideanSpace.basisFun Config ℂ n

/-- The canonical coordinate orthonormal basis of the finite Hilbert Fock space. -/
noncomputable def finiteHilbertOrthonormalBasis :
    OrthonormalBasis Config ℂ (FiniteHilbertFock Config) :=
  EuclideanSpace.basisFun Config ℂ

/-- The canonical coordinate Hilbert basis of the finite Hilbert Fock space. -/
noncomputable def finiteHilbertBasis :
    HilbertBasis Config ℂ (FiniteHilbertFock Config) :=
  (finiteHilbertOrthonormalBasis (Config := Config)).toHilbertBasis

@[simp]
theorem finiteHilbertOrthonormalBasis_apply (n : Config) :
    finiteHilbertOrthonormalBasis (Config := Config) n = finiteHilbertBasisState n :=
  rfl

@[simp]
theorem finiteHilbertBasis_apply (n : Config) :
    finiteHilbertBasis (Config := Config) n = finiteHilbertBasisState n :=
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
    QuantumTheory.TraceClass.DensityOperator (FiniteHilbertFock Config) :=
  diagonalDensityOperator
    (finiteHilbertBasis (Config := Config))
    (finiteBoltzmannWeight energy β)
    Summable.of_finite
    (fun n => (Real.exp_pos _).le)
    (finitePartitionFunction_pos energy β)

/-- The finite Gibbs density operator acts diagonally with normalized Boltzmann weights. -/
@[simp]
theorem finiteGibbsDensityOperator_apply_basis (energy : Config → ℝ) (β : ℝ) (n : Config) :
    (finiteGibbsDensityOperator energy β).op (finiteHilbertBasisState n) =
      (((finitePartitionFunction energy β)⁻¹ * finiteBoltzmannWeight energy β n : ℝ) : ℂ) •
        finiteHilbertBasisState n := by
  simpa [finiteGibbsDensityOperator, finitePartitionFunction, normalizedDiagonalWeight] using
    diagonalDensityOperator_apply_basis
      (finiteHilbertBasis (Config := Config))
      (finiteBoltzmannWeight energy β)
      (Summable.of_finite : Summable fun n : Config => ‖finiteBoltzmannWeight energy β n‖)
      (fun n => (Real.exp_pos _).le)
      (finitePartitionFunction_pos energy β) n

end
end Common
end SecondQuantization
