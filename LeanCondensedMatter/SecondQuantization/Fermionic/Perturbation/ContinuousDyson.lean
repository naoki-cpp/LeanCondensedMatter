import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonExponentialUniqueness
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture

set_option linter.style.header false

/-!
# Fermionic specializations of the continuous finite Dyson bridge

The analytic operator layer remains statistics-independent in `SecondQuantization.Common`. This
file only fixes `Config := FermionOccupation Mode` and `energy := fermionEnergy ε`, preserving the
existing algebraic fermionic API and diagrammatic declarations unchanged.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- The finite-dimensional normed realization of fermionic Fock space. -/
abbrev ContinuousFockSpaceFermionic (Mode : Type*) :=
  Common.FiniteAnalyticFock (FermionOccupation Mode)

/-- Continuous endomorphisms of the finite-dimensional fermionic realization. -/
abbrev ContinuousFermionOperator (Mode : Type*) :=
  Common.FiniteContinuousOperator (FermionOccupation Mode)

/-- Continuous realization of the free fermionic imaginary-time evolution. -/
noncomputable abbrev continuousImaginaryTimeEvolveFree (ε : Mode → ℝ) :=
  Common.continuousDiagonalEvolution (fermionEnergy ε)

/-- Continuous realization of the fermionic interaction-picture operator. -/
noncomputable abbrev continuousInteractionPicture (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :=
  Common.continuousInteractionPicture (fermionEnergy ε) V

/-- Continuous realization of the fermionic Dyson coefficients. -/
noncomputable abbrev continuousDysonCoeff (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :=
  Common.continuousDysonCoeff (fermionEnergy ε) V

/-- The canonical uniform interaction-picture norm bound for the fermionic specialization. -/
noncomputable abbrev interactionPictureNormBound (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :=
  Common.interactionPictureNormBound (fermionEnergy ε) V

/-- The perturbatively weighted fermionic Dyson term. -/
noncomputable abbrev analyticDysonTerm (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :=
  Common.analyticDysonTerm (fermionEnergy ε) V

/-- The norm-convergent fermionic interaction-picture Dyson evolution. -/
noncomputable abbrev analyticDysonEvolution (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :=
  Common.analyticDysonEvolution (fermionEnergy ε) V

/-- The continuous basis-diagonal free fermionic Hamiltonian. -/
noncomputable abbrev continuousDiagonalHamiltonian (ε : Mode → ℝ) :=
  Common.continuousDiagonalHamiltonian (fermionEnergy ε)

/-- The continuous interacting fermionic Hamiltonian `H₀ + λV`. -/
noncomputable abbrev continuousInteractingHamiltonian (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :=
  Common.continuousInteractingHamiltonian (fermionEnergy ε) V

/-- The exact ordered-exponential candidate for the fermionic analytic Dyson evolution. -/
noncomputable abbrev analyticDysonExponentialCandidate (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :=
  Common.analyticDysonExponentialCandidate (fermionEnergy ε) V

omit [LinearOrder Mode] in
@[simp]
theorem continuousDysonCoeff_zero (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τ : ℝ) :
    continuousDysonCoeff ε V 0 τ = 1 :=
  Common.continuousDysonCoeff_zero (fermionEnergy ε) V τ

omit [LinearOrder Mode] in
theorem continuousDysonCoeff_succ (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) (τ : ℝ) :
    continuousDysonCoeff ε V (n + 1) τ =
      - ∫ σ in (0 : ℝ)..τ,
          (continuousInteractionPicture ε V σ).comp
            (continuousDysonCoeff ε V n σ) :=
  Common.continuousDysonCoeff_succ (fermionEnergy ε) V n τ

omit [LinearOrder Mode] in
theorem continuous_continuousDysonCoeff (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    Continuous (continuousDysonCoeff ε V n) :=
  Common.continuous_continuousDysonCoeff (fermionEnergy ε) V n

omit [LinearOrder Mode] in
/-- Uniform fermionic interaction-picture norm control on `[0, β]`. -/
theorem norm_continuousInteractionPicture_le (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Set.Icc (0 : ℝ) β) :
    ‖continuousInteractionPicture ε V τ‖ ≤ interactionPictureNormBound ε V β :=
  Common.norm_continuousInteractionPicture_le (fermionEnergy ε) V hβ hτ

omit [LinearOrder Mode] in
/-- Factorial norm estimate for the fermionic continuous Dyson coefficients. -/
theorem norm_continuousDysonCoeff_le (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {β τ : ℝ}
    (hβ : 0 ≤ β) (n : ℕ) (hτ : τ ∈ Set.Icc (0 : ℝ) β) :
    ‖continuousDysonCoeff ε V n τ‖ ≤
      Common.dysonMajorant (interactionPictureNormBound ε V β) τ n :=
  Common.norm_continuousDysonCoeff_le (fermionEnergy ε) V hβ n hτ

omit [LinearOrder Mode] in
/-- Absolute summability of perturbatively weighted fermionic Dyson coefficients. -/
theorem summable_norm_pow_smul_continuousDysonCoeff (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Set.Icc (0 : ℝ) β) (lam : ℂ) :
    Summable (fun n : ℕ => ‖lam ^ n • continuousDysonCoeff ε V n τ‖) :=
  Common.summable_norm_pow_smul_continuousDysonCoeff (fermionEnergy ε) V hβ hτ lam

omit [LinearOrder Mode] in
/-- The fermionic analytic Dyson series has the declared operator-valued sum. -/
theorem hasSum_analyticDysonEvolution (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Set.Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum (analyticDysonTerm ε V τ lam)
      (analyticDysonEvolution ε V τ lam) :=
  Common.hasSum_analyticDysonEvolution (fermionEnergy ε) V hβ hτ lam

omit [LinearOrder Mode] in
/-- The fermionic analytic Dyson series converges uniformly on `[0, β]`. -/
theorem hasSumUniformlyOn_analyticDysonEvolution (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {β : ℝ}
    (hβ : 0 ≤ β) (lam : ℂ) :
    HasSumUniformlyOn
      (fun n τ => analyticDysonTerm ε V τ lam n)
      (fun τ => analyticDysonEvolution ε V τ lam)
      (Set.Icc (0 : ℝ) β) :=
  Common.hasSumUniformlyOn_analyticDysonEvolution (fermionEnergy ε) V hβ lam

omit [LinearOrder Mode] in
@[simp]
theorem analyticDysonEvolution_zero (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (lam : ℂ) :
    analyticDysonEvolution ε V 0 lam = 1 :=
  Common.analyticDysonEvolution_zero (fermionEnergy ε) V lam

omit [LinearOrder Mode] in
/-- The fermionic analytic Dyson evolution solves the interaction-picture Volterra equation. -/
theorem analyticDysonEvolution_eq_one_sub_integral (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Set.Icc (0 : ℝ) β) (lam : ℂ) :
    analyticDysonEvolution ε V τ lam =
      1 - lam • ∫ σ in (0 : ℝ)..τ,
        (continuousInteractionPicture ε V σ).comp
          (analyticDysonEvolution ε V σ lam) :=
  Common.analyticDysonEvolution_eq_one_sub_integral
    (fermionEnergy ε) V hβ hτ lam

omit [LinearOrder Mode] in
/-- The fermionic analytic Dyson sum equals the exact ordered-exponential candidate. -/
theorem analyticDysonEvolution_eq_exponentialCandidate (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Set.Icc (0 : ℝ) β) (lam : ℂ) :
    analyticDysonEvolution ε V τ lam =
      analyticDysonExponentialCandidate ε V τ lam :=
  Common.analyticDysonEvolution_eq_exponentialCandidate
    (fermionEnergy ε) V hβ hτ lam

omit [LinearOrder Mode] in
/-- Explicit ordered-exponential representation of the fermionic analytic Dyson evolution. -/
theorem analyticDysonEvolution_eq_ordered_exp (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    {τ : ℝ} (hτ : 0 ≤ τ) (lam : ℂ) :
    analyticDysonEvolution ε V τ lam =
      NormedSpace.exp (τ • continuousDiagonalHamiltonian ε) *
        NormedSpace.exp (τ • (- continuousInteractingHamiltonian ε V lam)) :=
  Common.analyticDysonEvolution_eq_ordered_exp (fermionEnergy ε) V hτ lam

omit [LinearOrder Mode] in
/-- At inverse temperature `β`, cancelling the free evolution gives the interacting Gibbs
exponential. -/
theorem continuousImaginaryTimeEvolveFree_neg_mul_analyticDysonEvolution_eq_exp
    (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    {β : ℝ} (hβ : 0 ≤ β) (lam : ℂ) :
    continuousImaginaryTimeEvolveFree ε (-β) *
        analyticDysonEvolution ε V β lam =
      NormedSpace.exp ((-β) • continuousInteractingHamiltonian ε V lam) :=
  Common.continuousDiagonalEvolution_neg_mul_analyticDysonEvolution_eq_exp
    (fermionEnergy ε) V hβ lam

end SecondQuantization
