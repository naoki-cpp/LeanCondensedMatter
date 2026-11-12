import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Interaction
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.OrderedProductSummable

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-Gibbs summability of bosonic quartic interactions

An ordered quartic vertex is a finite product of two creation and two annihilation fields.
The general free-thermal ordered-product summability theorem places it in the free-Gibbs domain
under positive one-mode Boltzmann exponents. Finite linear closure of that domain then promotes
single-vertex membership to finitely supported quartic interactions.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- Every finitely supported bosonic quartic interaction belongs to the free-Gibbs domain. -/
theorem quarticInteractionOn_mem_grandCanonicalGibbsDomain
    (support : Finset (QuarticVertexLabel Mode))
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (g : QuarticVertexLabel Mode → ℂ) :
    quarticInteractionOn support g ∈ grandCanonicalGibbsDomain ε β μ := by
  classical
  change (∑ q ∈ support, g q • quarticVertexOperator q) ∈ grandCanonicalGibbsDomain ε β μ
  exact Submodule.sum_mem (grandCanonicalGibbsDomain ε β μ) fun q hq =>
    (grandCanonicalGibbsDomain ε β μ).smul_mem (g q) (by
      simpa only [FreeThermalField.orderedProduct_cons, FreeThermalField.orderedProduct_nil,
        FreeThermalField.operator, LinearMap.comp_id,
        quarticVertexOperator, Common.quarticVertexOperator] using
        (FreeThermalField.orderedProduct_mem_grandCanonicalGibbsDomain ε β μ hpos
          [.create q.create₁, .create q.create₂, .annihilate q.annihilate₂,
            .annihilate q.annihilate₁]))

end
end Bosonic
end SecondQuantization
