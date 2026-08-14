import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentDecompositionEquiv

set_option linter.style.header false

/-!
# Quartic diagrams as a connected decomposition

The connected-component decomposition of a labelled quartic diagram depends only on its pairing and
connectivity structure. This adapter exposes `componentDecompositionEquiv` to the generic cumulant
`ConnectedDecomposition` API once, independently of particle statistics or operator realization.
-/

namespace SecondQuantization
namespace Common

noncomputable def quarticDiagramConnectedDecomposition
    (Label : Type*) [Fintype Label] (N : ℕ) :
    Combinatorics.ConnectedDecomposition (Fin N) where
  Object S := QuarticDiagram Label N S
  ConnectedObject S := ConnectedQuarticDiagram Label N S
  fintypeObject _ := inferInstance
  fintypeConnectedObject _ := inferInstance
  decompose _ := QuarticDiagram.componentDecompositionEquiv

end Common
end SecondQuantization
