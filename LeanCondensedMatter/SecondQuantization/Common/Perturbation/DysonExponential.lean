import LeanCondensedMatter.Analysis.Dyson.Uniqueness
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDyson
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Exponential realization of the interaction-picture Dyson evolution

For finite configuration spaces, the generic Dyson evolution driven by the transported
interaction-picture family is identified with the ordered product of the free and interacting
operator exponentials. Proof-only exponential candidates and their differential/Volterra
identities are kept private in this module.
-/

namespace SecondQuantization
namespace Common

open Set

noncomputable section

variable {Config : Type*} [Fintype Config]

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

/-- The exact operator-exponential candidate for the interaction-picture Dyson evolution. -/
private noncomputable def dysonExponentialCandidate (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) : FiniteContinuousOperator Config :=
  NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
    NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam))

/-- Multiplying the exact candidate by the interaction-picture operator cancels the two free
propagators in the middle. -/
private theorem continuousInteractionPicture_mul_dysonExponentialCandidate
    (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) :
    continuousInteractionPicture energy V τ *
        dysonExponentialCandidate energy V τ lam =
      continuousDiagonalEvolution energy τ *
        (finiteContinuousOperatorAlgEquiv V *
          NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam))) := by
  rw [continuousInteractionPicture_eq_conj, dysonExponentialCandidate,
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
private theorem hasDerivAt_dysonExponentialCandidate_raw (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) :
    HasDerivAt (fun σ : ℝ => dysonExponentialCandidate energy V σ lam)
      ((NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          continuousDiagonalHamiltonian energy) *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) +
        NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          ((- continuousInteractingHamiltonian energy V lam) *
            NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)))) τ := by
  unfold dysonExponentialCandidate
  exact (hasDerivAt_exp_smul_const (continuousDiagonalHamiltonian energy) τ).mul
    (hasDerivAt_exp_smul_const' (- continuousInteractingHamiltonian energy V lam) τ)

/-- The exact candidate solves the same interaction-picture differential equation as the Dyson
series. -/
private theorem hasDerivAt_dysonExponentialCandidate_interactionPicture
    (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) :
    HasDerivAt (fun σ : ℝ => dysonExponentialCandidate energy V σ lam)
      (-(lam • (continuousInteractionPicture energy V τ *
        dysonExponentialCandidate energy V τ lam))) τ := by
  have hderiv :
      NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
          (-(lam • finiteContinuousOperatorAlgEquiv V)) *
          NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) =
        -(lam • (continuousInteractionPicture energy V τ *
          dysonExponentialCandidate energy V τ lam)) := by
    rw [continuousInteractionPicture_mul_dysonExponentialCandidate]
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
  convert hasDerivAt_dysonExponentialCandidate_raw energy V τ lam using 1
  rw [continuousInteractingHamiltonian]
  noncomm_ring


/-- The exact operator-exponential candidate satisfies its interaction-picture Volterra equation,
by the fundamental theorem of calculus. -/
private theorem dysonExponentialCandidate_eq_one_sub_integral (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (lam : ℂ) :
    dysonExponentialCandidate energy V τ lam =
      1 - lam • ∫ σ in (0 : ℝ)..τ,
        continuousInteractionPicture energy V σ *
          dysonExponentialCandidate energy V σ lam := by
  let U : ℝ → FiniteContinuousOperator Config :=
    fun σ => dysonExponentialCandidate energy V σ lam
  let f : ℝ → FiniteContinuousOperator Config :=
    fun σ => -(lam • (continuousInteractionPicture energy V σ * U σ))
  have hderiv : ∀ σ ∈ uIcc (0 : ℝ) τ, HasDerivAt U (f σ) σ := by
    intro σ _
    exact hasDerivAt_dysonExponentialCandidate_interactionPicture
      energy V σ lam
  have hUcont : Continuous U := by
    exact continuous_iff_continuousAt.2 fun σ =>
      (hasDerivAt_dysonExponentialCandidate_interactionPicture
        energy V σ lam).continuousAt
  have hf : Continuous f := by
    have hlam : Continuous (fun _ : ℝ => lam) := continuous_const
    exact (hlam.smul
      ((continuous_continuousInteractionPicture energy V).mul hUcont)).neg
  have hFTC : (∫ σ in (0 : ℝ)..τ, f σ) = U τ - U 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hf.intervalIntegrable 0 τ)
  have hzero : U 0 = 1 := by
    simp [U, dysonExponentialCandidate]
  rw [hzero] at hFTC
  have hFTC' :
      -(lam • ∫ σ in (0 : ℝ)..τ, continuousInteractionPicture energy V σ * U σ) =
        U τ - 1 := by
    simpa only [f, intervalIntegral.integral_neg, intervalIntegral.integral_smul] using hFTC
  change U τ = 1 - lam • ∫ σ in (0 : ℝ)..τ,
    continuousInteractionPicture energy V σ * U σ
  calc
    U τ = 1 + (U τ - 1) := by abel
    _ = 1 + (-(lam • ∫ σ in (0 : ℝ)..τ,
          continuousInteractionPicture energy V σ * U σ)) := by rw [← hFTC']
    _ = 1 - lam • ∫ σ in (0 : ℝ)..τ,
          continuousInteractionPicture energy V σ * U σ := by abel

/-- On every compact nonnegative time interval, the interaction-picture Dyson evolution equals
the exact ordered operator-exponential candidate. -/
private theorem dysonEvolution_eq_exponentialCandidate (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    Dyson.evolution (continuousInteractionPicture energy V) lam τ =
      dysonExponentialCandidate energy V τ lam := by
  have hUcont : Continuous
      (fun t : ℝ => dysonExponentialCandidate energy V t lam) := by
    exact continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_dysonExponentialCandidate_interactionPicture
        energy V t lam).continuousAt
  obtain ⟨M, hBound⟩ := Dyson.exists_continuousBoundedInteraction
    (continuousInteractionPicture energy V) hβ
    (continuous_continuousInteractionPicture energy V)
    ContinuousLinearMap.norm_id_le
  have hEq := Dyson.eqOn_evolution_of_volterra_of_bound
    (V := continuousInteractionPicture energy V)
    (U := fun t : ℝ => dysonExponentialCandidate energy V t lam)
    hβ hBound lam
    hUcont.continuousOn
    (fun t _ => dysonExponentialCandidate_eq_one_sub_integral energy V t lam)
  change Dyson.evolution (continuousInteractionPicture energy V) lam τ =
    dysonExponentialCandidate energy V τ lam
  exact (hEq hτ).symm

/-- For nonnegative imaginary time, the interaction-picture Dyson evolution is the ordered product
of the free and interacting operator exponentials. -/
theorem dysonEvolution_eq_ordered_exp (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    {τ : ℝ} (hτ : 0 ≤ τ) (lam : ℂ) :
    Dyson.evolution (continuousInteractionPicture energy V) lam τ =
      NormedSpace.exp (τ • continuousDiagonalHamiltonian energy) *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian energy V lam)) := by
  simpa [dysonExponentialCandidate] using
    dysonEvolution_eq_exponentialCandidate
      (β := τ) (τ := τ) energy V hτ ⟨hτ, le_rfl⟩ lam

/-- At the thermal endpoint, left multiplication by the inverse free evolution leaves the
interacting Gibbs exponential. -/
theorem continuousDiagonalEvolution_neg_mul_dysonEvolution_eq_exp
    (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    {β : ℝ} (hβ : 0 ≤ β) (lam : ℂ) :
    continuousDiagonalEvolution energy (-β) *
        Dyson.evolution (continuousInteractionPicture energy V) lam β =
      NormedSpace.exp ((-β) • continuousInteractingHamiltonian energy V lam) := by
  rw [dysonEvolution_eq_ordered_exp energy V hβ lam]
  rw [← continuousDiagonalEvolution_eq_exp energy β]
  have hinv :
      continuousDiagonalEvolution energy (-β) *
        continuousDiagonalEvolution energy β = 1 := by
    change (continuousDiagonalEvolution energy (-β)).comp
      (continuousDiagonalEvolution energy β) = 1
    exact continuousDiagonalEvolution_neg_comp energy β
  rw [← mul_assoc, hinv, one_mul]
  congr 1
  simp [smul_neg, neg_smul]


end
end Common
end SecondQuantization
