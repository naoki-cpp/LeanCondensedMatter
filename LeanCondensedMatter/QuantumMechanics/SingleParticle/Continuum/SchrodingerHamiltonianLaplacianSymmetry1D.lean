import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerHamiltonianClosedH21D
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Symmetry of the one-dimensional `H²` Laplacian

The distributional `H²` Laplacian has the expected real Fourier symbol

`-(2π)² |ξ|²`.

We first identify the Fourier transform of the `L²` Laplacian representative almost everywhere,
using uniqueness of locally integrable functions that define the same distribution. Plancherel then
turns the reality of the Fourier symbol into symmetry of the `H²` Laplacian.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal MeasureTheory InnerProductSpace SchwartzMap Laplacian LineDeriv Real

private def laplacianFourierSymbol1D (x : ℝ) : ℂ :=
  ((-((2 * Real.pi) ^ 2) * ‖x‖ ^ 2 : ℝ) : ℂ)

private theorem continuous_laplacianFourierSymbol1D :
    Continuous laplacianFourierSymbol1D := by
  unfold laplacianFourierSymbol1D
  fun_prop

private theorem laplacianFourierSymbol1D_hasTemperateGrowth :
    laplacianFourierSymbol1D.HasTemperateGrowth := by
  unfold laplacianFourierSymbol1D
  fun_prop

private theorem inner_laplacianFourierSymbol1D_mul
    (x : ℝ) (z w : ℂ) :
    inner ℂ (laplacianFourierSymbol1D x * z) w =
      inner ℂ z (laplacianFourierSymbol1D x * w) := by
  let r : ℝ := -((2 * Real.pi) ^ 2) * ‖x‖ ^ 2
  change inner ℂ ((r : ℂ) • z) w = inner ℂ z ((r : ℂ) • w)
  rw [inner_smul_left, inner_smul_right]
  simp

/-- Fourier-transforming the distributional `H²` Laplacian gives multiplication by the usual
real Laplacian symbol. This statement is still at the tempered-distribution level. -/
theorem fourier_l2ToTemperedDistribution1D_continuumH2Laplacian1D
    (ψ : continuumH2Domain1D) :
    𝓕 (l2ToTemperedDistribution1D (continuumH2Laplacian1D ψ)) =
      (-(2 * Real.pi) ^ 2 : ℂ) •
        TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => Complex.ofReal (‖x‖ ^ 2))
          (𝓕 (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D))) := by
  rw [l2ToTemperedDistribution1D_continuumH2Laplacian1D,
    TemperedDistribution.laplacian_eq_fourierMultiplierCLM,
    TemperedDistribution.fourierMultiplierCLM_apply,
    ← Complex.coe_smul (-(2 * Real.pi) ^ 2),
    FourierTransform.fourier_smul, FourierTransform.fourier_fourierInv_eq]
  push_cast
  rfl

private theorem ae_eq_mul_of_l2ToTemperedDistribution_eq_smulLeft
    (u v : ContinuumL2Wavefunction1D) (g : ℝ → ℂ) (hg : g.HasTemperateGrowth)
    (h : l2ToTemperedDistribution1D u =
      TemperedDistribution.smulLeftCLM ℂ g (l2ToTemperedDistribution1D v)) :
    (fun x => u x) =ᵐ[volume] fun x => g x * v x := by
  have huLoc : LocallyIntegrable (fun x => u x) (volume : Measure ℝ) :=
    (Lp.memLp u).locallyIntegrable (by norm_num)
  have hvLoc : LocallyIntegrable (fun x => v x) (volume : Measure ℝ) :=
    (Lp.memLp v).locallyIntegrable (by norm_num)
  have hgvLoc : LocallyIntegrable (fun x => g x * v x) (volume : Measure ℝ) := by
    rw [← locallyIntegrableOn_univ]
    exact (hvLoc.locallyIntegrableOn Set.univ).continuousOn_mul hg.1.continuous.continuousOn
      (isOpen_univ.isLocallyClosed)
  apply ae_eq_of_integral_contDiff_smul_eq huLoc hgvLoc
  intro test htest hsupp
  let testC : ℝ → ℂ := Complex.ofRealCLM ∘ test
  have htestC_support : HasCompactSupport testC := hsupp.comp_left rfl
  let testS : SchwartzMap ℝ ℂ :=
    htestC_support.toSchwartzMap (Complex.ofRealCLM.contDiff.comp htest)
  calc
    ∫ x, test x • u x = l2ToTemperedDistribution1D u testS := by
      simp [l2ToTemperedDistribution1D, testS, testC]
    _ = TemperedDistribution.smulLeftCLM ℂ g
          (l2ToTemperedDistribution1D v) testS := by rw [h]
    _ = ∫ x, test x • (g x * v x) := by
      rw [TemperedDistribution.smulLeftCLM_apply_apply]
      simp only [l2ToTemperedDistribution1D, MeasureTheory.Lp.toTemperedDistributionCLM_apply,
        MeasureTheory.Lp.toTemperedDistribution_apply]
      apply integral_congr_ae
      filter_upwards with x
      rw [SchwartzMap.smulLeftCLM_apply hg]
      simp [testS, testC, mul_assoc, mul_left_comm]

/-- On `H²`, the Fourier transform of the `L²` Laplacian representative agrees almost everywhere
with multiplication by `-(2π)² |ξ|²`. -/
theorem fourier_continuumH2Laplacian1D_ae
    (ψ : continuumH2Domain1D) :
    (fun x => (𝓕 (continuumH2Laplacian1D ψ) : ContinuumL2Wavefunction1D) x) =ᵐ[volume]
      fun x => laplacianFourierSymbol1D x *
        (𝓕 (ψ : ContinuumL2Wavefunction1D) : ContinuumL2Wavefunction1D) x := by
  apply ae_eq_mul_of_l2ToTemperedDistribution_eq_smulLeft
    (𝓕 (continuumH2Laplacian1D ψ) : ContinuumL2Wavefunction1D)
    (𝓕 (ψ : ContinuumL2Wavefunction1D) : ContinuumL2Wavefunction1D)
    laplacianFourierSymbol1D laplacianFourierSymbol1D_hasTemperateGrowth
  have hleft :
      l2ToTemperedDistribution1D
          (𝓕 (continuumH2Laplacian1D ψ) : ContinuumL2Wavefunction1D) =
        𝓕 (l2ToTemperedDistribution1D (continuumH2Laplacian1D ψ)) := by
    simpa [l2ToTemperedDistribution1D] using
      (MeasureTheory.Lp.fourier_toTemperedDistribution_eq
        (continuumH2Laplacian1D ψ)).symm
  have hright :
      l2ToTemperedDistribution1D
          (𝓕 (ψ : ContinuumL2Wavefunction1D) : ContinuumL2Wavefunction1D) =
        𝓕 (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)) := by
    simpa [l2ToTemperedDistribution1D] using
      (MeasureTheory.Lp.fourier_toTemperedDistribution_eq
        (ψ : ContinuumL2Wavefunction1D)).symm
  rw [hleft, hright, fourier_l2ToTemperedDistribution1D_continuumH2Laplacian1D]
  change
    (((-(2 * Real.pi) ^ 2 : ℂ) •
        TemperedDistribution.smulLeftCLM ℂ
          (fun x : ℝ => Complex.ofReal (‖x‖ ^ 2)))
      (𝓕 (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)))) =
      TemperedDistribution.smulLeftCLM ℂ laplacianFourierSymbol1D
        (𝓕 (l2ToTemperedDistribution1D (ψ : ContinuumL2Wavefunction1D)))
  rw [← TemperedDistribution.smulLeftCLM_smul (F := ℂ) (by fun_prop)
    (-(2 * Real.pi) ^ 2 : ℂ)]
  congr 2
  funext x
  simp [laplacianFourierSymbol1D]

/-- The distributional Laplacian on the explicit `H²` domain is symmetric in the physical
`L²` inner product. -/
theorem continuumH2Laplacian1D_symmetric
    (ψ φ : continuumH2Domain1D) :
    inner ℂ (continuumH2Laplacian1D ψ) (φ : ContinuumL2Wavefunction1D) =
      inner ℂ (ψ : ContinuumL2Wavefunction1D) (continuumH2Laplacian1D φ) := by
  calc
    inner ℂ (continuumH2Laplacian1D ψ) (φ : ContinuumL2Wavefunction1D) =
        inner ℂ (𝓕 (continuumH2Laplacian1D ψ) : ContinuumL2Wavefunction1D)
          (𝓕 (φ : ContinuumL2Wavefunction1D) : ContinuumL2Wavefunction1D) :=
      (MeasureTheory.Lp.inner_fourier_eq
        (continuumH2Laplacian1D ψ) (φ : ContinuumL2Wavefunction1D)).symm
    _ = inner ℂ (𝓕 (ψ : ContinuumL2Wavefunction1D) : ContinuumL2Wavefunction1D)
          (𝓕 (continuumH2Laplacian1D φ) : ContinuumL2Wavefunction1D) := by
      rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [fourier_continuumH2Laplacian1D_ae ψ,
        fourier_continuumH2Laplacian1D_ae φ] with x hψ hφ
      rw [hψ, hφ]
      exact inner_laplacianFourierSymbol1D_mul x
        ((𝓕 (ψ : ContinuumL2Wavefunction1D) : ContinuumL2Wavefunction1D) x)
        ((𝓕 (φ : ContinuumL2Wavefunction1D) : ContinuumL2Wavefunction1D) x)
    _ = inner ℂ (ψ : ContinuumL2Wavefunction1D) (continuumH2Laplacian1D φ) :=
      MeasureTheory.Lp.inner_fourier_eq
        (ψ : ContinuumL2Wavefunction1D) (continuumH2Laplacian1D φ)

/-- The explicit `H²` Laplacian is a formal adjoint of itself. -/
theorem continuumH2LaplacianPMap1D_isFormalAdjoint :
    continuumH2LaplacianPMap1D.IsFormalAdjoint continuumH2LaplacianPMap1D := by
  intro ψ φ
  simpa [continuumH2LaplacianPMap1D] using continuumH2Laplacian1D_symmetric ψ φ

end
end Continuum
end SingleParticle
end QuantumMechanics
