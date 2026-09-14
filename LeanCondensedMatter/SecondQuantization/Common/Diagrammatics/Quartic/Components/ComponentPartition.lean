import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Connected
import LeanCondensedMatter.Combinatorics.SimpleGraphComponentPartition

set_option linter.style.header false

/-!
# Connected-component partitions of labelled quartic diagrams

Connected-component blocks and their finite partition depend only on the diagram's pairing graph,
not on the vertex-label type or particle statistics. The diagram-facing API keeps parts in the
ambient type `Fin N`, while graph/setoid construction and reachability lemmas are owned by
`Combinatorics`.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- The partition of `S` into connected components of the diagram's vertex graph. -/
noncomputable def QuarticDiagram.componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) : Finpartition S :=
  d.vertexGraph.componentPartitionOn

/-- The component containing `v`, viewed as a finite subset of the ambient vertex type. -/
noncomputable def QuarticDiagram.componentBlock {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (v : ↥S) : Finset (Fin N) :=
  d.componentPartition.part (v : Fin N)

end Common
end SecondQuantization
