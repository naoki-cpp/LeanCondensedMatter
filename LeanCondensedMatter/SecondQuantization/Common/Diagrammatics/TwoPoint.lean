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
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalConnectivity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.SlotCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedOrderPairing

set_option linter.style.header false

/-!
# Statistics-independent two-point diagrammatics

Paired diagrams with two external legs and quartic vertices: connectivity, separating propagators,
cut order, interval pairings, 1PI criteria, and mixed-order pairing transport.
The two external vertices belong to the same component by even leg parity. General external/vacuum
factorization is provided by `Common.Diagrammatics.ExternalInsertion`.
-/
