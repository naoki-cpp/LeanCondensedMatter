import LeanCondensedMatter.Combinatorics.FinpartitionProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentConnected

set_option linter.style.header false

/-!
# Products of vertex-local weights over quartic-diagram components

The connected-component partition of a quartic diagram decomposes its ambient vertices into the
dependent disjoint union of the component vertex sets. Applying finite-partition product identities
to this decomposition factors arbitrary commutative vertex-local weights over the components.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- The statistics-independent complex Dyson sign times vertex weight factors over connected
components. -/
theorem QuarticDiagram.dysonSign_mul_vertexWeight_eq_prod_components
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (w : Label → ℂ) :
    (-1 : ℂ) ^ S.card * d.vertexWeight w =
      ∏ B : d.vertexGraph.componentPartitionOn.parts,
        ((-1 : ℂ) ^ (B : Finset (Fin N)).card *
          ((d.restrictComponentConnected B.2).1).vertexWeight w) := by
  have hsign :
      (-1 : ℂ) ^ S.card =
        ∏ B : d.vertexGraph.componentPartitionOn.parts, (-1 : ℂ) ^ (B : Finset (Fin N)).card := by
    simpa using (Finpartition.pow_card_eq_prod_parts d.vertexGraph.componentPartitionOn (-1 : ℂ))
  have hweight :
      d.vertexWeight w =
        ∏ B : d.vertexGraph.componentPartitionOn.parts,
          ((d.restrictComponentConnected B.2).1).vertexWeight w := by
    simpa only [QuarticDiagram.vertexWeight, QuarticDiagram.restrictComponentConnected,
      QuarticDiagram.restrictComponent_vertexLabel_equivSigmaParts] using
      (Fintype.prod_equiv_sigma d.vertexGraph.componentPartitionOn.equivSigmaParts
        (fun v => w (d.vertexLabel v)))
  rw [hsign, hweight, Finset.prod_mul_distrib]

end Common
end SecondQuantization
