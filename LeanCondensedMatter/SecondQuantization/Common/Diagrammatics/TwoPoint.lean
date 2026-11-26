import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.ExternalInsertionBridge
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.OneParticleIrreducible
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.CutComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.SeparatingPaths
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.CutSides
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.CutOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.CutIntervals
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.IntervalPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.IntervalConnectivity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalConnectivity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotLegSplitting
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalSlotSplit
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitConnectivity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.SlotCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPosition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedOrderPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalPiece

set_option linter.style.header false

/-!
# Statistics-independent two-point diagrammatics

This package contains the combinatorial infrastructure for paired diagrams with two distinguished
one-legged external vertices and quartic interaction vertices. It does not attach operator
amplitudes or choose bosonic or fermionic statistics.

A special feature of the two-point family is that the two external vertices are automatically in
the same connected component: a component containing exactly one external leg would have an odd
number of legs and therefore could not carry a perfect pairing. Hence, for two-point diagrams,
external connectedness is equivalent to the absence of vacuum components.

The subpackages separate the main combinatorial responsibilities:

* `Core` defines the diagram syntax, flattened leg enumeration, vertex graph, and the semantic
  predicates for vacuum-free and externally connected diagrams.
* `Components` restricts connected components, identifies the canonical external component and
  vacuum components, and provides componentwise finite-sum and finite-product decompositions.
* `External` isolates the external component, splits its interaction slots from the vacuum
  remainder, and packages its standalone external piece and mixed-position embedding.
* `SlotSplit` compares the ambient two-point graph with its external/vacuum slot decomposition.
  Ordered vacuum pairing and component-pair factorization belong to the general external-insertion theory.
* `Mixed` transports the fixed pairing to mixed imaginary-time order. Component-local normalized
  pair decomposition, exchange signs and chamber locality are owned by general external insertions.

The representation is intentionally kept distinct from `ExternalInsertionDiagram`. The two
families share lower-level component and leg-data machinery, while the mature two-point API keeps
its own canonical normal forms for the downstream two-point expansion.
-/
