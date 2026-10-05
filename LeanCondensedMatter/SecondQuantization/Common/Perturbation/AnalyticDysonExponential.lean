import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDyson
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

variable {Config : Type*} [Fintype Config]

/-- The continuous realization of the basis-diagonal free Hamiltonian. -/
noncomputable def continuousDiagonalHamiltonian (energy : Config → ℝ) :
    FiniteContinuousOperator Config :=
  finiteContinuousOperatorAlgEquiv (diagonalOperator fun c => (energy c : ℂ))

@[simp]
private theorem continuousDiagonalHamiltonian_basis_apply (energy : Config → ℝ) (c : Config) :
    continuousDiagonalHamiltonian energy (finiteAnalyticBasis c) =
      (energy c : ℂ) • finiteAnalyticBasis c := by
  calc
    continuousDiagonalHamiltonian energy (finiteAnalyticBasis c) =
        finiteAnalyticFockEquiv
          (diagonalOperator (fun c => (energy c : ℂ)) (basisState c)) := by
      rw [continuousDiagonalHamiltonian, ← finiteAnalyticFockEquiv_basisState,
        finiteContinuousOperator_equiv_apply]
    _ = (energy c : ℂ) • finiteAnalyticBasis c := by
      rw [diagonalOperator_basisState, map_smul, finiteAnalyticFockEquiv_basisState]

private theorem smul_continuousDiagonalHamiltonian_basis_apply (energy : Config → ℝ)
    (τ : ℝ) (c : Config) :
    (τ • continuousDiagonalHamiltonian energy) (finiteAnalyticBasis c) =
      ((τ * energy c : ℝ) : ℂ) • finiteAnalyticBasis c := by
  change (τ : ℂ) • continuousDiagonalHamiltonian energy (finiteAnalyticBasis c) = _
  rw [continuousDiagonalHamiltonian_basis_apply, smul_smul, Complex.ofReal_mul]

private theorem smul_continuousDiagonalHamiltonian_pow_basis_apply (energy : Config → ℝ)
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
private theorem exp_continuousDiagonalHamiltonian_basis_apply (energy : Config → ℝ)
    (τ : ℝ) (c : Config) :
    NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) (finiteAnalyticBasis c) =
      Complex.exp ((τ * energy c : ℝ) : ℂ) • finiteAnalyticBasis c := by
  let evalBasis : FiniteContinuousOperator Config →L[ℂ] FiniteAnalyticFock Config :=
    ContinuousLinearMap.apply ℂ (FiniteAnalyticFock Config) (finiteAnalyticBasis c)
  let spanBasis : ℂ →L[ℂ] FiniteAnalyticFock Config :=
    ContinuousLinearMap.toSpanSingleton ℂ (finiteAnalyticBasis c)
  have hop := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
    (τ • continuousDiagonalHamiltonian energy)).map evalBasis evalBasis.continuous
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
    (((τ * energy c : ℝ) : ℂ))).map spanBasis spanBasis.continuous
  have hterms :
      (evalBasis ∘ fun n : ℕ =>
        ((Nat.factorial n : ℂ)⁻¹) • (τ • continuousDiagonalHamiltonian energy) ^ n) =
      (spanBasis ∘ fun n : ℕ =>
        ((Nat.factorial n : ℂ)⁻¹) • (((τ * energy c : ℝ) : ℂ) ^ n)) := by
    funext n
    change ((Nat.factorial n : ℂ)⁻¹) •
        ((τ • continuousDiagonalHamiltonian energy) ^ n) (finiteAnalyticBasis c) =
      (((Nat.factorial n : ℂ)⁻¹ * (((τ * energy c : ℝ) : ℂ) ^ n)) •
        finiteAnalyticBasis c)
    rw [smul_continuousDiagonalHamiltonian_pow_basis_apply, smul_smul]
  rw [hterms] at hop
  have heq := hop.unique hscalar
  simpa [evalBasis, spanBasis, Complex.exp_eq_exp_ℂ] using heq

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
  continuousDiagonalHamiltonian energy + lam • finiteContinuousOperatorAlgEquiv V

/-- The exact operator-exponential candidate for the interaction-picture Dyson evolution. -/
noncomputable def analyticDysonExponentialCandidate (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) : FiniteContinuousOperator Config :=
  NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
    NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam))

@[simp]
theorem analyticDysonExponentialCandidate_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    analyticDysonExponentialCandidate energy V 0 lam = 1 := by
  simp [analyticDysonExponentialCandidate]

/-- Multiplying the exact candidate by the interaction-picture operator cancels the two free
propagators in the middle. -/
private theorem continuousInteractionPicture_mul_analyticDysonExponentialCandidate
    (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) :
    continuousInteractionPicture energy V τ *
        analyticDysonExponentialCandidate energy V τ lam =
      continuousDiagonalEvolution energy τ *
        (finiteContinuousOperatorAlgEquiv V *
          NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam))) := by
  rw [continuousInteractionPicture_eq_conj, analyticDysonExponentialCandidate,
    ← continuousDiagonalEvolution_eq_exp energy τ]
  change
    (continuousDiagonalEvolution energy τ *
      (finiteContinuousOperatorAlgEquiv V * continuousDiagonalEvolution energy (-τ))) *
      (continuousDiagonalEvolution energy τ *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam))) =
    continuousDiagonalEvolution energy τ *
      (finiteContinuousOperatorAlgEquiv V *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)))
  have hinv :
      continuousDiagonalEvolution energy (-τ) *
        continuousDiagonalEvolution energy τ = 1 := by
    change (continuousDiagonalEvolution energy (-τ)).comp
      (continuousDiagonalEvolution energy τ) = 1
    exact continuousDiagonalEvolution_neg_comp energy τ
  calc
    _ = continuousDiagonalEvolution energy τ * finiteContinuousOperatorAlgEquiv V *
        (continuousDiagonalEvolution energy (-τ) *
          continuousDiagonalEvolution energy τ) *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) := by
      noncomm_ring
    _ = continuousDiagonalEvolution energy τ * finiteContinuousOperatorAlgEquiv V * 1 *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) := by
      rw [hinv]
    _ = _ := by noncomm_ring

/-- Product-rule derivative of the exponential candidate, before cancellation of the free
Hamiltonian terms. -/
private theorem hasDerivAt_analyticDysonExponentialCandidate_raw (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) :
    HasDerivAt (fun σ : ℝ => analyticDysonExponentialCandidate energy V σ lam)
      ((NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          continuousDiagonalHamiltonian energy) *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) +
        NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          ((- continuousInteractingHamiltonian energy V lam) *
            NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)))) τ := by
  unfold analyticDysonExponentialCandidate
  exact (hasDerivAt_exp_smul_const (continuousDiagonalHamiltonian energy) τ).mul
    (hasDerivAt_exp_smul_const' (- continuousInteractingHamiltonian energy V lam) τ)

/-- The exact candidate solves the same interaction-picture differential equation as the Dyson
series. -/
theorem hasDerivAt_analyticDysonExponentialCandidate_interactionPicture
    (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) :
    HasDerivAt (fun σ : ℝ => analyticDysonExponentialCandidate energy V σ lam)
      (-(lam • (continuousInteractionPicture energy V τ *
        analyticDysonExponentialCandidate energy V τ lam))) τ := by
  have hderiv :
      NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          (-(lam • finiteContinuousOperatorAlgEquiv V)) *
          NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) =
        -(lam • (continuousInteractionPicture energy V τ *
          analyticDysonExponentialCandidate energy V τ lam)) := by
    rw [continuousInteractionPicture_mul_analyticDysonExponentialCandidate]
    calc
      NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          (-(lam • finiteContinuousOperatorAlgEquiv V)) *
          NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) =
        -(lam • (NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          finiteContinuousOperatorAlgEquiv V)) *
          NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) := by
        rw [mul_neg, mul_smul_comm]
      _ = -(lam • ((NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          finiteContinuousOperatorAlgEquiv V) *
          NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)))) := by
        rw [neg_mul, smul_mul_assoc]
      _ = -(lam • (NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          (finiteContinuousOperatorAlgEquiv V *
            NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam))))) := by
        rw [mul_assoc]
      _ = -(lam • (continuousDiagonalEvolution energy τ *
          (finiteContinuousOperatorAlgEquiv V *
            NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam))))) := by
        rw [continuousDiagonalEvolution_eq_exp]
  rw [← hderiv]
  convert hasDerivAt_analyticDysonExponentialCandidate_raw energy V τ lam using 1
  rw [continuousInteractingHamiltonian]
  noncomm_ring

end
end Common
end SecondQuantization
