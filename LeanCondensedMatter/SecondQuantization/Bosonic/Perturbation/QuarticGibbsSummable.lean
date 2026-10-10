import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Interaction
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.OrderedProductSummable

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-Gibbs summability of bosonic quartic interactions

An ordered quartic vertex is a finite product of two creation and two annihilation fields.
The general free-thermal ordered-product summability theorem places it in the free-Gibbs domain
under positive one-mode Boltzmann exponents. Finite linear closure of that domain then promotes
single-vertex membership to finitely supported quartic interactions and, for finite mode types,
to the all-label quartic interaction.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- A single ordered quartic vertex belongs to the explicit free-Gibbs domain under the usual
positive one-mode Boltzmann exponents. -/
theorem quarticVertexOperator_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (q : QuarticVertexLabel Mode) :
    quarticVertexOperator q ∈ freeGibbsDomain ε β := by
  change freeGibbsSummable ε β (quarticVertexOperator q)
  simpa only [FreeThermalField.orderedProduct_cons, FreeThermalField.orderedProduct_nil,
    FreeThermalField.operator, LinearMap.comp_id,
    quarticVertexOperator, Common.quarticVertexOperator] using
    (FreeThermalField.freeGibbsSummable_orderedProduct ε β hpos
      [.create q.create₁, .create q.create₂, .annihilate q.annihilate₂, .annihilate q.annihilate₁])

/-- Every finitely supported bosonic quartic interaction belongs to the free-Gibbs domain. -/
theorem quarticInteractionOn_mem_freeGibbsDomain
    (support : Finset (QuarticVertexLabel Mode))
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) :
    quarticInteractionOn support g ∈ freeGibbsDomain ε β := by
  classical
  change (∑ q ∈ support, g q • quarticVertexOperator q) ∈ freeGibbsDomain ε β
  exact Submodule.sum_mem (freeGibbsDomain ε β) fun q hq =>
    (freeGibbsDomain ε β).smul_mem (g q)
      (quarticVertexOperator_mem_freeGibbsDomain ε β hpos q)

/-- On a finite mode type, the all-label bosonic quartic interaction belongs to the free-Gibbs
domain. -/
theorem quarticInteraction_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) :
    quarticInteraction g ∈ freeGibbsDomain ε β := by
  simpa [quarticInteraction, quarticInteractionOn, Common.quarticInteraction] using
    (quarticInteractionOn_mem_freeGibbsDomain
      (support := (Finset.univ : Finset (QuarticVertexLabel Mode))) ε β hpos g)

end
end Bosonic
end SecondQuantization
