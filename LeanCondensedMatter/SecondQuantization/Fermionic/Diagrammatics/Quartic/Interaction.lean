import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic

set_option linter.style.header false

/-!
# A fixed-arity number-conserving quartic interaction

The concrete fermionic interaction operator used by the Wick-diagram layer is a generally
non-diagonal number-conserving quartic vertex `Σ g(q) cᵢ†cⱼ†cₗcₖ`.

The fixed operator-ordering convention is
`quarticVertexOperator q := c_{q.create₁}† c_{q.create₂}† c_{q.annihilate₂} c_{q.annihilate₁}`.
The statistics-independent constructor and its free-evolution proof are inherited from
`SecondQuantization.Common`; fermionic CAR consequences remain in the fermionic layer.

For an infinite mode type, `quarticInteractionOn support g` constructs the operator from any finite
set of active quartic labels. The all-label `quarticInteraction g` remains the finite-mode
specialization.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- Compatibility alias for the statistics-independent quartic vertex label. -/
abbrev QuarticVertexLabel (Mode : Type*) := Common.QuarticVertexLabel Mode

/-- **The quartic vertex operator**, in the fixed creation-creation-annihilation-annihilation order. -/
noncomputable def quarticVertexOperator (q : QuarticVertexLabel Mode) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.quarticVertexOperator create annihilate q

/-- A fermionic quartic interaction supported on a finite set of vertex labels. -/
noncomputable def quarticInteractionOn (support : Finset (QuarticVertexLabel Mode))
    (g : QuarticVertexLabel Mode → ℂ) : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.quarticInteractionOn support create annihilate g

/-- **The all-label quartic interaction** on a finite mode type. -/
noncomputable def quarticInteraction [Fintype Mode] (g : QuarticVertexLabel Mode → ℂ) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.quarticInteraction create annihilate g

/-- **A single quartic vertex's interaction-picture expansion** with the total free-energy shift. -/
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

/-- **The quartic interaction's interaction-picture expansion** as the evolved all-label finite sum. -/
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
