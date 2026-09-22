import LeanCondensedMatter.SecondQuantization.Common.Interaction.Quartic
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution

set_option linter.style.header false

/-!
# Imaginary-time evolution of generic quartic interactions

The quartic interaction constructors are owned by `Common.Interaction.Quartic`. This module contains
the generic diagonal Heisenberg-evolution results for quartic local legs and vertices.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Mode Config : Type*}

namespace QuarticLocalLeg

/-- A local quartic leg assembled from ladder eigenoperators evolves with its signed energy shift. -/
theorem heisenbergEvolve_operator
    (energy : Config → ℝ) (ε : Mode → ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (leg : QuarticLocalLeg Mode) (τ : ℝ)
    (hcreate : ∀ i, heisenbergEvolve energy τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i)
    (hannihilate : ∀ i, heisenbergEvolve energy τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i) :
    heisenbergEvolve energy τ (leg.operator create annihilate) =
      Complex.exp (((τ * leg.energyShift ε : ℝ) : ℂ)) •
        leg.operator create annihilate := by
  cases leg <;> simp [hcreate, hannihilate, mul_comm]

end QuarticLocalLeg

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
  simp only [quarticVertexOperator, ← Module.End.mul_eq_comp, map_mul]
  rw [hcreate, hcreate, hannihilate, hannihilate]
  simp only [Module.End.mul_eq_comp, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [quarticVertexEnergyShift]
  push_cast
  ring

end
end Common
end SecondQuantization
