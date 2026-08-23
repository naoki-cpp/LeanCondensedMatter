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

theorem smul_continuousDiagonalHamiltonian_basis_apply (energy : Config → ℝ)
    (τ : ℝ) (c : Config) :
    (τ • continuousDiagonalHamiltonian energy) (finiteAnalyticBasis c) =
      ((τ * energy c : ℝ) : ℂ) • finiteAnalyticBasis c := by
  change (τ : ℂ) • continuousDiagonalHamiltonian energy (finiteAnalyticBasis c) = _
  rw [continuousDiagonalHamiltonian_basis_apply, smul_smul, Complex.ofReal_mul]

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
  continuousDiagonalHamiltonian energy + lam • finiteContinuousOperator V

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

/-- Rewrite the exact candidate with the existing continuous free evolution. -/
theorem analyticDysonExponentialCandidate_eq (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) :
    analyticDysonExponentialCandidate energy V τ lam =
      continuousDiagonalEvolution energy τ *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) := by
  rw [analyticDysonExponentialCandidate, continuousDiagonalEvolution_eq_exp]

/-- Multiplying the exact candidate by the interaction-picture operator cancels the two free
propagators in the middle. -/
theorem continuousInteractionPicture_mul_analyticDysonExponentialCandidate
    (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) :
    continuousInteractionPicture energy V τ *
        analyticDysonExponentialCandidate energy V τ lam =
      continuousDiagonalEvolution energy τ *
        (finiteContinuousOperator V *
          NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam))) := by
  rw [continuousInteractionPicture_eq_conj,
    analyticDysonExponentialCandidate_eq]
  change
    (continuousDiagonalEvolution energy τ *
      (finiteContinuousOperator V * continuousDiagonalEvolution energy (-τ))) *
      (continuousDiagonalEvolution energy τ *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam))) =
    continuousDiagonalEvolution energy τ *
      (finiteContinuousOperator V *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)))
  have hinv :
      continuousDiagonalEvolution energy (-τ) *
        continuousDiagonalEvolution energy τ = 1 := by
    change (continuousDiagonalEvolution energy (-τ)).comp
      (continuousDiagonalEvolution energy τ) = 1
    exact continuousDiagonalEvolution_neg_comp energy τ
  calc
    _ = continuousDiagonalEvolution energy τ * finiteContinuousOperator V *
        (continuousDiagonalEvolution energy (-τ) *
          continuousDiagonalEvolution energy τ) *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) := by
      noncomm_ring
    _ = continuousDiagonalEvolution energy τ * finiteContinuousOperator V * 1 *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) := by
      rw [hinv]
    _ = _ := by noncomm_ring

/-- Product-rule derivative of the exponential candidate, before cancellation of the free
Hamiltonian terms. -/
theorem hasDerivAt_analyticDysonExponentialCandidate_raw (energy : Config → ℝ)
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

/-- After cancellation of the free Hamiltonian, the candidate derivative contains only the
interaction insertion. -/
theorem hasDerivAt_analyticDysonExponentialCandidate (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) :
    HasDerivAt (fun σ : ℝ => analyticDysonExponentialCandidate energy V σ lam)
      (NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
        (-(lam • finiteContinuousOperator V)) *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam))) τ := by
  convert hasDerivAt_analyticDysonExponentialCandidate_raw energy V τ lam using 1
  rw [continuousInteractingHamiltonian]
  noncomm_ring

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
          (-(lam • finiteContinuousOperator V)) *
          NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) =
        -(lam • (continuousInteractionPicture energy V τ *
          analyticDysonExponentialCandidate energy V τ lam)) := by
    rw [continuousInteractionPicture_mul_analyticDysonExponentialCandidate]
    calc
      NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          (-(lam • finiteContinuousOperator V)) *
          NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) =
        -(lam • (NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          finiteContinuousOperator V)) *
          NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) := by
        rw [mul_neg, mul_smul_comm]
      _ = -(lam • ((NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          finiteContinuousOperator V) *
          NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)))) := by
        rw [neg_mul, smul_mul_assoc]
      _ = -(lam • (NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          (finiteContinuousOperator V *
            NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam))))) := by
        rw [mul_assoc]
      _ = -(lam • (continuousDiagonalEvolution energy τ *
          (finiteContinuousOperator V *
            NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam))))) := by
        rw [continuousDiagonalEvolution_eq_exp]
  rw [← hderiv]
  exact hasDerivAt_analyticDysonExponentialCandidate energy V τ lam

end
end Common
end SecondQuantization
