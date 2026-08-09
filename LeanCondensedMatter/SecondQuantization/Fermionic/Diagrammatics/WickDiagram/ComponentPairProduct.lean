import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentPairProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairValue

set_option linter.style.header false

/-!
# Component-local fermionic pair-product factorization

Statistics-independent component-pair reindexing lives in `SecondQuantization.Common`.  This file
contains only the fermionic pair-value specialization used by the contraction integrand.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} {N : ℕ}

section Fermionic

variable [LinearOrder Mode] [Fintype Mode]

/-- The product of pair values in an assembled global order is the iterated product of the
component-local pair values. -/
theorem QuarticWickDiagram.prod_orderedQuarticPairValue_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) (τ : Fin S.card → ℝ) :
    (∏ pr : d.GlobalOrderedPair orders shuffle,
      orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ pr.1.1 pr.1.2) =
      ∏ B : d.componentPartition.parts,
        ∏ pr : d.LocalOrderedPair orders B,
          orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
            (d.componentTimeAssignment shuffle τ B) pr.1.1 pr.1.2 := by
  rw [d.prod_componentPairs orders shuffle]
  apply Fintype.prod_congr
  intro B
  apply Fintype.prod_congr
  intro pr
  rw [d.componentPairEquiv_apply orders shuffle B pr]
  exact orderedQuarticPairValue_componentOrderedLeg
    ε β d orders shuffle τ B pr.1.1 pr.1.2

/-- The pair-value product factorization in the same nested-Finset form used by
`QuarticWickDiagram.contractionIntegrand`. -/
theorem QuarticWickDiagram.prod_orderedQuarticPairValue_pairs_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) (τ : Fin S.card → ℝ) :
    (∏ pr ∈ (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs,
      orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ pr.1 pr.2) =
      ∏ B : d.componentPartition.parts,
        ∏ pr ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs,
          orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
            (d.componentTimeAssignment shuffle τ B) pr.1 pr.2 := by
  classical
  calc
    (∏ pr ∈ (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs,
        orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ pr.1 pr.2) =
        (∏ pr : d.GlobalOrderedPair orders shuffle,
          orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle)
            τ pr.1.1 pr.1.2) :=
      Finset.prod_subtype _ (fun _ => Iff.rfl) _
    _ = ∏ B : d.componentPartition.parts,
        ∏ pr : d.LocalOrderedPair orders B,
          orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
            (d.componentTimeAssignment shuffle τ B) pr.1.1 pr.1.2 :=
      d.prod_orderedQuarticPairValue_eq_prod_components ε β orders shuffle τ
    _ = ∏ B : d.componentPartition.parts,
        ∏ pr ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs,
          orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
            (d.componentTimeAssignment shuffle τ B) pr.1 pr.2 := by
      apply Fintype.prod_congr
      intro B
      exact (Finset.prod_subtype
        ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs
        (fun _ => Iff.rfl)
        (fun pr => orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
          (d.componentTimeAssignment shuffle τ B) pr.1 pr.2)).symm

end Fermionic

end Fermionic
end SecondQuantization
