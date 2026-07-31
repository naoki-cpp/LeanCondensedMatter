import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonVolterra
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option linter.style.header false

/-!
# Operator-exponential realization of the analytic Dyson evolution

This module places the basis-diagonal free Hamiltonian and the interacting Hamiltonian in the same
finite-dimensional continuous-operator algebra as `analyticDysonEvolution`. The exact
interaction-picture candidate is then the ordered product

`exp (τ H₀) * exp (-τ (H₀ + λ V))`.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*}

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
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

variable [Fintype Config]

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

@[simp]
theorem continuousDiagonalHamiltonian_pow_basis_apply (energy : Config → ℝ)
    (c : Config) (n : ℕ) :
    (continuousDiagonalHamiltonian energy ^ n) (finiteAnalyticBasis c) =
      (energy c : ℂ) ^ n • finiteAnalyticBasis c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change continuousDiagonalHamiltonian energy
        ((continuousDiagonalHamiltonian energy ^ n) (finiteAnalyticBasis c)) = _
      rw [ih, map_smul, continuousDiagonalHamiltonian_basis_apply, smul_smul]
      simp [pow_succ]

@[simp]
theorem smul_continuousDiagonalHamiltonian_basis_apply (energy : Config → ℝ)
    (τ : ℝ) (c : Config) :
    (τ • continuousDiagonalHamiltonian energy) (finiteAnalyticBasis c) =
      ((τ * energy c : ℝ) : ℂ) • finiteAnalyticBasis c := by
  change τ • continuousDiagonalHamiltonian energy (finiteAnalyticBasis c) = _
  rw [continuousDiagonalHamiltonian_basis_apply]
  simp [smul_smul]

@[simp]
theorem smul_continuousDiagonalHamiltonian_pow_basis_apply (energy : Config → ℝ)
    (τ : ℝ) (c : Config) (n : ℕ) :
    ((τ • continuousDiagonalHamiltonian energy) ^ n) (finiteAnalyticBasis c) =
      (((τ * energy c : ℝ) : ℂ) ^ n) • finiteAnalyticBasis c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change (τ • continuousDiagonalHamiltonian energy)
        (((τ • continuousDiagonalHamiltonian energy) ^ n) (finiteAnalyticBasis c)) = _
      rw [ih, map_smul, smul_continuousDiagonalHamiltonian_basis_apply, smul_smul]
      rw [pow_succ]

/-- The Banach-algebra exponential of the free Hamiltonian acts diagonally with the expected
scalar exponential. -/
theorem exp_continuousDiagonalHamiltonian_basis_apply (energy : Config → ℝ)
    (τ : ℝ) (c : Config) :
    NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) (finiteAnalyticBasis c) =
      Complex.exp ((τ * energy c : ℝ) : ℂ) • finiteAnalyticBasis c := by
  let evalBasis : FiniteContinuousOperator Config →L[ℂ] FiniteAnalyticFock Config :=
    ContinuousLinearMap.apply ℂ (FiniteAnalyticFock Config) (finiteAnalyticBasis c)
  have hop := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
    (τ • continuousDiagonalHamiltonian energy)).map evalBasis
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
    (((τ * energy c : ℝ) : ℂ))).map
      (ContinuousLinearMap.toSpanSingleton ℂ (finiteAnalyticBasis c))
  have hterms :
      (fun n : ℕ => evalBasis
        (((Nat.factorial n : ℂ)⁻¹) • (τ • continuousDiagonalHamiltonian energy) ^ n)) =
      (fun n : ℕ => ContinuousLinearMap.toSpanSingleton ℂ (finiteAnalyticBasis c)
        (((Nat.factorial n : ℂ)⁻¹) • (((τ * energy c : ℝ) : ℂ) ^ n))) := by
    funext n
    simp [evalBasis, smul_continuousDiagonalHamiltonian_pow_basis_apply, smul_smul]
  rw [hterms] at hop
  have heq := hop.unique hscalar
  simpa [evalBasis, Complex.exp_eq_exp_ℂ] using heq

/-- The continuous free evolution is the Banach-algebra exponential of the diagonal
Hamiltonian. -/
theorem continuousDiagonalEvolution_eq_exp (energy : Config → ℝ) (τ : ℝ) :
    continuousDiagonalEvolution energy τ =
      NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) := by
  apply finiteContinuousOperator_ext_basis
  intro c
  rw [continuousDiagonalEvolution_basis_apply,
    exp_continuousDiagonalHamiltonian_basis_apply]

/-- The interacting Hamiltonian `H₀ + λV` in the finite continuous-operator algebra. -/
noncomputable def continuousInteractingHamiltonian (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    FiniteContinuousOperator Config :=
  continuousDiagonalHamiltonian energy + lam • finiteContinuousOperator V

/-- The exact operator-exponential candidate for the interaction-picture Dyson evolution. -/
noncomputable def analyticDysonExponentialCandidate (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) : FiniteContinuousOperator Config :=
  NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
    NormedSpace.exp ((-τ) • continuousInteractingHamiltonian energy V lam)

@[simp]
theorem analyticDysonExponentialCandidate_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    analyticDysonExponentialCandidate energy V 0 lam = 1 := by
  simp [analyticDysonExponentialCandidate]

end
end Common
end SecondQuantization
