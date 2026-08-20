import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic

set_option linter.style.header false

/-!
# Bosonic quartic interaction vertices

A quartic vertex carries two creation modes and two annihilation modes. The operator order is fixed
as `a†_{create₁} a†_{create₂} a_{annihilate₂} a_{annihilate₁}`, matching the fermionic quartic
vertex convention while using bosonic ladder operators. The statistics-independent constructor
and its free-evolution proof are inherited from `SecondQuantization.Common`.

For an infinite mode type, `quarticInteractionOn support g` constructs the operator from a finite set
of active quartic labels. The all-label `quarticInteraction g` remains the finite-mode specialization.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*}

/-- Compatibility alias for the statistics-independent quartic vertex label. -/
abbrev QuarticVertexLabel (Mode : Type*) := Common.QuarticVertexLabel Mode

/-- The ordered bosonic quartic vertex operator. -/
noncomputable def quarticVertexOperator (q : QuarticVertexLabel Mode) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.quarticVertexOperator create annihilate q

/-- A bosonic quartic interaction supported on a finite set of vertex labels. -/
noncomputable def quarticInteractionOn (support : Finset (QuarticVertexLabel Mode))
    (g : QuarticVertexLabel Mode → ℂ) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.quarticInteractionOn support create annihilate g

/-- The all-label bosonic quartic interaction on a finite mode type. -/
noncomputable def quarticInteraction [Fintype Mode] (g : QuarticVertexLabel Mode → ℂ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.quarticInteraction create annihilate g

/-- A single bosonic quartic vertex evolves by its total free-energy shift. -/
theorem interactionPicture_quarticVertexOperator (ε : Mode → ℝ) (q : QuarticVertexLabel Mode)
    (τ : ℝ) :
    interactionPicture ε (quarticVertexOperator q) τ =
      Complex.exp (((τ : ℂ)) * ((ε q.create₁ : ℂ) + (ε q.create₂ : ℂ) -
        (ε q.annihilate₁ : ℂ) - (ε q.annihilate₂ : ℂ))) • quarticVertexOperator q := by
  simpa [interactionPicture, Common.interactionPicture, quarticVertexOperator,
    Common.quarticVertexEnergyShift] using
    (Common.heisenbergEvolve_quarticVertexOperator
      (freeEigenvalue ε) ε create annihilate q τ
      (fun i => imaginaryTimeEvolve_create ε τ i)
      (fun i => imaginaryTimeEvolve_annihilate ε τ i))

/-- The interaction picture distributes over the all-label finite-mode quartic interaction. -/
theorem interactionPicture_quarticInteraction [Fintype Mode] (ε : Mode → ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (τ : ℝ) :
    interactionPicture ε (quarticInteraction g) τ =
      ∑ q, g q • interactionPicture ε (quarticVertexOperator q) τ := by
  simpa [interactionPicture, Common.interactionPicture, quarticInteraction,
    quarticVertexOperator] using
    (Common.heisenbergEvolve_quarticInteraction
      (freeEigenvalue ε) τ create annihilate g)

end Bosonic
end SecondQuantization
