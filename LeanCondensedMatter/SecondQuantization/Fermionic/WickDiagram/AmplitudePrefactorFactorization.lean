import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.Amplitude

set_option linter.style.header false

/-!
# Component factorization of quartic Wick-amplitude prefactors

This is the scalar-prefactor part of Wick-diagram amplitude factorization. The coupling product and
Dyson recursion sign already factor over connected components. The remaining analytic step is the
shuffle identity for the vertex-order sum of ordered-simplex contributions.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- The product of quartic couplings factors over the connected-component restrictions. -/
theorem QuarticWickDiagram.couplingWeight_eq_prod_restrictComponentConnected
    [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (g : QuarticVertexLabel Mode → ℂ) :
    d.couplingWeight g =
      ∏ B : d.componentPartition.parts,
        QuarticWickDiagram.couplingWeight ((d.restrictComponentConnected B.2).1) g := by
  simpa only [QuarticWickDiagram.couplingWeight,
    QuarticWickDiagram.restrictComponentConnected] using
      (Common.QuarticDiagram.prod_vertexLabel_eq_prod_restrictComponent (d := d) (w := g))

/-- The Dyson recursion sign `(-1)^|S|` is the product of the corresponding signs on the component
blocks. -/
theorem QuarticWickDiagram.dysonSign_eq_prod_componentSigns
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) :
    (-1 : ℂ) ^ S.card =
      ∏ B : d.componentPartition.parts, (-1 : ℂ) ^ (B : Finset (Fin N)).card :=
  Common.QuarticDiagram.dysonSign_eq_prod_componentSigns d

/-- The complete scalar prefactor of `quarticWickDiagramAmplitude` factors over connected
components. What remains for the full amplitude theorem is the vertex-order/ordered-simplex shuffle
factorization. -/
theorem QuarticWickDiagram.amplitudePrefactor_eq_prod_restrictComponentConnected
    [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (g : QuarticVertexLabel Mode → ℂ) :
    (-1 : ℂ) ^ S.card * d.couplingWeight g =
      ∏ B : d.componentPartition.parts,
        ((-1 : ℂ) ^ (B : Finset (Fin N)).card *
          QuarticWickDiagram.couplingWeight ((d.restrictComponentConnected B.2).1) g) := by
  rw [d.dysonSign_eq_prod_componentSigns, d.couplingWeight_eq_prod_restrictComponentConnected]
  rw [Finset.prod_mul_distrib]

end SecondQuantization
