import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonVolterra
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option linter.style.header false

/-!
# Operator-exponential realization of the analytic Dyson evolution

This module places the basis-diagonal free Hamiltonian and the interacting Hamiltonian in the same
finite-dimensional continuous-operator algebra as `analyticDysonEvolution`.  The exact
interaction-picture candidate is then the ordered product

`exp (τ H₀) * exp (-τ (H₀ + λ V))`.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The algebraic basis-diagonal Hamiltonian with eigenvalue `energy c` on `basisState c`. -/
noncomputable def diagonalHamiltonian (energy : Config → ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  Finsupp.lift (AlgebraicFock Config) ℂ Config
    (fun c => (energy c : ℂ) • basisState c)

@[simp]
theorem diagonalHamiltonian_basisState (energy : Config → ℝ) (c : Config) :
    diagonalHamiltonian energy (basisState c) =
      (energy c : ℂ) • basisState c := by
  change Finsupp.lift _ ℂ _ _ (Finsupp.single c 1) = _
  simp [diagonalHamiltonian, Finsupp.lift_apply, Finsupp.sum_single_index]

/-- The continuous realization of the basis-diagonal free Hamiltonian. -/
noncomputable def continuousDiagonalHamiltonian (energy : Config → ℝ) :
    FiniteContinuousOperator Config :=
  finiteContinuousOperator (diagonalHamiltonian energy)

@[simp]
theorem continuousDiagonalHamiltonian_basis_apply (energy : Config → ℝ) (c : Config) :
    continuousDiagonalHamiltonian energy (finiteAnalyticBasis c) =
      (energy c : ℂ) • finiteAnalyticBasis c := by
  calc
    continuousDiagonalHamiltonian energy (finiteAnalyticBasis c) =
        finiteAnalyticFockEquiv
          (diagonalHamiltonian energy (basisState c)) := by
      rw [continuousDiagonalHamiltonian, ← finiteAnalyticFockEquiv_basisState,
        finiteContinuousOperator_equiv_apply]
    _ = (energy c : ℂ) • finiteAnalyticBasis c := by
      rw [diagonalHamiltonian_basisState, map_smul, finiteAnalyticFockEquiv_basisState]

/-- The interacting Hamiltonian `H₀ + λV` in the finite continuous-operator algebra. -/
noncomputable def continuousInteractingHamiltonian (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    FiniteContinuousOperator Config :=
  continuousDiagonalHamiltonian energy + lam • finiteContinuousOperator V

/-- The exact operator-exponential candidate for the interaction-picture Dyson evolution. -/
noncomputable def analyticDysonExponentialCandidate (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) : FiniteContinuousOperator Config :=
  NormedSpace.exp ((τ : ℂ) • continuousDiagonalHamiltonian energy) *
    NormedSpace.exp ((-(τ : ℂ)) • continuousInteractingHamiltonian energy V lam)

@[simp]
theorem analyticDysonExponentialCandidate_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    analyticDysonExponentialCandidate energy V 0 lam = 1 := by
  simp [analyticDysonExponentialCandidate]

end
end Common
end SecondQuantization
