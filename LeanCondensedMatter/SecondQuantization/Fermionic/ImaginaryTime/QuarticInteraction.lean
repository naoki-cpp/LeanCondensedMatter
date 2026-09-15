import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture

set_option linter.style.header false

/-!
# Imaginary-time evolution of fermionic quartic interactions

The algebraic quartic operators are owned by `Fermionic.Algebra.QuarticInteraction`. This module
contains only their fermionic imaginary-time evolution statements.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- A single quartic vertex is an eigenoperator of the free interaction-picture evolution with its
total free-energy shift. -/
theorem interactionPicture_quarticVertexOperator (ε : Mode → ℝ) (q : QuarticVertexLabel Mode)
    (τ : ℝ) :
    interactionPicture ε (quarticVertexOperator q) τ =
      Complex.exp (((τ : ℂ)) * ((ε q.create₁ : ℂ) + (ε q.create₂ : ℂ) - (ε q.annihilate₁ : ℂ) -
        (ε q.annihilate₂ : ℂ))) • quarticVertexOperator q := by
  simpa [interactionPicture, Common.interactionPicture, quarticVertexOperator,
    Common.quarticVertexEnergyShift] using
    (Common.heisenbergEvolve_quarticVertexOperator
      (fermionEnergy ε) ε create annihilate q τ
      (fun i => imaginaryTimeEvolve_create ε τ i)
      (fun i => imaginaryTimeEvolve_annihilate ε τ i))

/-- The all-label quartic interaction evolves as the finite sum of its evolved vertices. -/
theorem interactionPicture_quarticInteraction [Fintype Mode] (ε : Mode → ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (τ : ℝ) :
    interactionPicture ε (quarticInteraction g) τ =
      ∑ q, g q • interactionPicture ε (quarticVertexOperator q) τ := by
  simpa [interactionPicture, Common.interactionPicture, quarticInteraction,
    quarticVertexOperator] using
    (Common.heisenbergEvolve_quarticInteraction
      (fermionEnergy ε) τ create annihilate g)

end Fermionic
end SecondQuantization
