import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticDiagramComponentDecompositionEquiv

set_option linter.style.header false

/-!
# Bosonic quartic-diagram scalar weights

The coupling product and Dyson recursion sign are the statistics-independent scalar prefactor that a
future bosonic Wick amplitude will carry. Both factor over the connected-component decomposition.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} {N : ℕ}

/-- The product of the quartic coupling over all vertices of a bosonic diagram. -/
noncomputable def QuarticDiagram.couplingWeight {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) (g : QuarticVertexLabel Mode → ℂ) : ℂ :=
  ∏ v : ↥S, g (d.vertexLabel v)

/-- The bosonic quartic coupling weight factors over connected-component restrictions. -/
theorem QuarticDiagram.couplingWeight_eq_prod_restrictComponentConnected
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (g : QuarticVertexLabel Mode → ℂ) :
    d.couplingWeight g =
      ∏ B : d.componentPartition.parts,
        QuarticDiagram.couplingWeight ((d.restrictComponentConnected B.2).1) g := by
  simpa only [QuarticDiagram.couplingWeight, QuarticDiagram.restrictComponentConnected,
    Common.QuarticDiagram.restrictComponentConnected] using
      (Common.QuarticDiagram.prod_vertexLabel_eq_prod_restrictComponent (d := d) (w := g))

/-- The Dyson recursion sign factors over the connected components of a bosonic quartic diagram. -/
theorem QuarticDiagram.dysonSign_eq_prod_componentSigns
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S) :
    (-1 : ℂ) ^ S.card =
      ∏ B : d.componentPartition.parts, (-1 : ℂ) ^ (B : Finset (Fin N)).card :=
  Common.QuarticDiagram.dysonSign_eq_prod_componentSigns d

/-- The scalar prefactor expected in a bosonic quartic Wick amplitude factors over connected
components. -/
theorem QuarticDiagram.amplitudePrefactor_eq_prod_restrictComponentConnected
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (g : QuarticVertexLabel Mode → ℂ) :
    (-1 : ℂ) ^ S.card * d.couplingWeight g =
      ∏ B : d.componentPartition.parts,
        ((-1 : ℂ) ^ (B : Finset (Fin N)).card *
          QuarticDiagram.couplingWeight ((d.restrictComponentConnected B.2).1) g) := by
  rw [d.dysonSign_eq_prod_componentSigns, d.couplingWeight_eq_prod_restrictComponentConnected]
  rw [Finset.prod_mul_distrib]

end Bosonic
end SecondQuantization
