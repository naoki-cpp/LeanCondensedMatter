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
theorem quarticVertexOperator_mem_grandCanonicalGibbsDomain
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (q : QuarticVertexLabel Mode) :
    quarticVertexOperator q ∈ grandCanonicalGibbsDomain ε β μ := by
  change grandCanonicalGibbsSummable ε β μ (quarticVertexOperator q)
  simpa only [FreeThermalField.orderedProduct_cons, FreeThermalField.orderedProduct_nil,
    FreeThermalField.operator, LinearMap.comp_id,
    quarticVertexOperator, Common.quarticVertexOperator] using
    (FreeThermalField.grandCanonicalGibbsSummable_orderedProduct ε β μ hpos
      [.create q.create₁, .create q.create₂, .annihilate q.annihilate₂, .annihilate q.annihilate₁])

/-- Every finitely supported bosonic quartic interaction belongs to the free-Gibbs domain. -/
theorem quarticInteractionOn_mem_grandCanonicalGibbsDomain
    (support : Finset (QuarticVertexLabel Mode))
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (g : QuarticVertexLabel Mode → ℂ) :
    quarticInteractionOn support g ∈ grandCanonicalGibbsDomain ε β μ := by
  classical
  change (∑ q ∈ support, g q • quarticVertexOperator q) ∈ grandCanonicalGibbsDomain ε β μ
  exact Submodule.sum_mem (grandCanonicalGibbsDomain ε β μ) fun q hq =>
    (grandCanonicalGibbsDomain ε β μ).smul_mem (g q)
      (quarticVertexOperator_mem_grandCanonicalGibbsDomain ε β μ hpos q)

/-- On a finite mode type, the all-label bosonic quartic interaction belongs to the free-Gibbs
domain. -/
theorem quarticInteraction_mem_grandCanonicalGibbsDomain
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (g : QuarticVertexLabel Mode → ℂ) :
    quarticInteraction g ∈ grandCanonicalGibbsDomain ε β μ := by
  simpa [quarticInteraction, quarticInteractionOn, Common.quarticInteraction] using
    (quarticInteractionOn_mem_grandCanonicalGibbsDomain
      (support := (Finset.univ : Finset (QuarticVertexLabel Mode))) ε β μ hpos g)

end
end Bosonic
end SecondQuantization
