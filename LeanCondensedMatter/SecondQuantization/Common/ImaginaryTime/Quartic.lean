import LeanCondensedMatter.SecondQuantization.Common.Interaction.Quartic
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution

set_option linter.style.header false

/-!
# Imaginary-time evolution of generic quartic interactions

The quartic interaction constructors are owned by `Common.Interaction.Quartic`. This module contains
the generic diagonal Heisenberg-evolution results for quartic local legs, vertices, and finite
interaction sums.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Mode Config : Type*}

/-- A local quartic leg assembled from ladder eigenoperators evolves with its signed energy shift. -/
theorem heisenbergEvolve_quarticLocalLegOperator
    (energy : Config → ℝ) (ε : Mode → ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : QuarticVertexLabel Mode) (l : Fin 4) (τ : ℝ)
    (hcreate : ∀ i, heisenbergEvolve energy τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i)
    (hannihilate : ∀ i, heisenbergEvolve energy τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i) :
    heisenbergEvolve energy τ (quarticLocalLegOperator create annihilate q l) =
      Complex.exp (((τ * quarticLocalLegEnergyShift ε q l : ℝ) : ℂ)) •
        quarticLocalLegOperator create annihilate q l := by
  fin_cases l <;>
    simp [quarticLocalLegOperator, quarticLocalLegEnergyShift, hcreate, hannihilate, mul_comm]

/-- A quartic vertex assembled from ladder eigenoperators evolves with their total energy shift. -/
theorem heisenbergEvolve_quarticVertexOperator
    (energy : Config → ℝ) (ε : Mode → ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : QuarticVertexLabel Mode) (τ : ℝ)
    (hcreate : ∀ i, heisenbergEvolve energy τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i)
    (hannihilate : ∀ i, heisenbergEvolve energy τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i) :
    heisenbergEvolve energy τ (quarticVertexOperator create annihilate q) =
      Complex.exp ((τ : ℂ) * (quarticVertexEnergyShift ε q : ℂ)) •
        quarticVertexOperator create annihilate q := by
  simp only [quarticVertexOperator, heisenbergEvolve_comp]
  rw [hcreate, hcreate, hannihilate, hannihilate]
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [quarticVertexEnergyShift]
  push_cast
  ring

/-- Diagonal Heisenberg evolution distributes over a finitely supported quartic interaction. -/
theorem heisenbergEvolve_quarticInteractionOn
    (support : Finset (QuarticVertexLabel Mode)) (energy : Config → ℝ) (τ : ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (g : QuarticVertexLabel Mode → ℂ) :
    heisenbergEvolve energy τ (quarticInteractionOn support create annihilate g) =
      ∑ q ∈ support, g q • heisenbergEvolve energy τ (quarticVertexOperator create annihilate q) := by
  rw [quarticInteractionOn, heisenbergEvolve_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [heisenbergEvolve_smul]

/-- Diagonal Heisenberg evolution distributes over the all-label finite-mode interaction. -/
theorem heisenbergEvolve_quarticInteraction [Fintype Mode]
    (energy : Config → ℝ) (τ : ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (g : QuarticVertexLabel Mode → ℂ) :
    heisenbergEvolve energy τ (quarticInteraction create annihilate g) =
      ∑ q, g q • heisenbergEvolve energy τ (quarticVertexOperator create annihilate q) := by
  simpa [quarticInteraction] using
    (heisenbergEvolve_quarticInteractionOn
      (support := (Finset.univ : Finset (QuarticVertexLabel Mode))) energy τ create annihilate g)

end
end Common
end SecondQuantization
