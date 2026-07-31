import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDysonBounds
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansion

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

end SecondQuantization
