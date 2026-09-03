import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Hamiltonian.MaximalLaplacian1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Maximal-Laplacian regularity in one dimension

For the Bessel-potential convention used by Mathlib,

`B₂ = 1 - (2π)⁻² Δ`.

Consequently, an `L²` tempered distribution whose distributional Laplacian also has an `L²`
representative already belongs to `H²`. This closes the regularity gap between the explicit `H²`
domain and the maximal distributional Laplacian domain.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory SchwartzMap Laplacian LineDeriv Real

private theorem besselPotential_two_eq_sub_laplacian (f : 𝓢'(ℝ, ℂ)) :
    TemperedDistribution.besselPotential ℝ ℂ 2 f =
      f - (((2 * Real.pi) ^ 2 : ℝ)⁻¹) • Δ f := by
  rw [TemperedDistribution.besselPotential,
    TemperedDistribution.laplacian_eq_fourierMultiplierCLM]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hcoef :
      (((2 * Real.pi) ^ 2 : ℝ)⁻¹) * (-((2 * Real.pi) ^ 2 : ℝ)) = -1 := by
    field_simp [hpi]
  rw [smul_smul, hcoef, neg_one_smul, sub_neg_eq_add]
  have hconst :
      TemperedDistribution.fourierMultiplierCLM ℂ (fun _ : ℝ => (1 : ℂ)) f = f := by
    simp
  rw [← hconst]
  have hsymbol :
      (fun x : ℝ => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2))) =
        (fun _ : ℝ => (1 : ℂ)) +
          (fun x : ℝ => Complex.ofReal (‖x‖ ^ 2)) := by
    funext x
    norm_num
  rw [hsymbol]
  simp only [TemperedDistribution.fourierMultiplierCLM_apply]
  rw [TemperedDistribution.smulLeftCLM_add (F := ℂ)
    (g₁ := fun _ : ℝ => (1 : ℂ))
    (g₂ := fun x : ℝ => Complex.ofReal (‖x‖ ^ 2)) (by fun_prop) (by fun_prop)]
  simp

/-- If an `L²` wavefunction has an `L²` distributional Laplacian, then it belongs to `H²`. -/
theorem continuumMaximalLaplacianDomain1D_le_continuumH2Domain1D :
    continuumMaximalLaplacianDomain1D ≤ continuumH2Domain1D := by
  intro ψ hψ
  rw [mem_continuumH2Domain1D_iff]
  obtain ⟨φ, hφ⟩ :=
    (mem_continuumMaximalLaplacianDomain1D_iff ψ).mp hψ
  rw [TemperedDistribution.MemSobolev]
  let c : ℝ := ((2 * Real.pi) ^ 2)⁻¹
  refine ⟨ψ - c • φ, ?_⟩
  change TemperedDistribution.besselPotential ℝ ℂ 2
      (l2ToTemperedDistribution1D ψ) =
    l2ToTemperedDistribution1D (ψ - c • φ)
  rw [besselPotential_two_eq_sub_laplacian, ← hφ, map_sub,
    l2ToTemperedDistribution1D.map_smul_of_tower]

/-- The explicit `H²` domain equals the maximal distributional Laplacian domain. -/
theorem continuumH2Domain1D_eq_continuumMaximalLaplacianDomain1D :
    continuumH2Domain1D = continuumMaximalLaplacianDomain1D :=
  le_antisymm continuumH2Domain1D_le_continuumMaximalLaplacianDomain1D
    continuumMaximalLaplacianDomain1D_le_continuumH2Domain1D

end
end Continuum
end SingleParticle
end QuantumMechanics
