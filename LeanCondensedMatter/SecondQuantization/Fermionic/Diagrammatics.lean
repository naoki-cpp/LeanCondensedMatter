import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointWickDiagram
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Amplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairValue
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentContractionIntegrand
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.AmplitudeFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonConnectedDiagramExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonLinkedClusterTheorem
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonLinkedClusterLowOrder

set_option linter.style.header false

/-!
# Fermionic diagrammatics

Quartic interaction vertices, the two-point external-leg foundation and atomic mixed-time-order
flattening, local-leg semantics, ordered Wick diagrams and amplitudes, component orders,
order-preserving shuffle decompositions, shuffled ordered-simplex integrands, component-local leg,
pairing and fermionic contraction-integrand specialization, and full quartic Wick-amplitude
factorization over connected components; the Dyson diagram expansion, the connected-diagram formula
for Dyson vertex cumulants, the general algebraic Dyson Linked Cluster Theorem, and its explicit
orders-one-through-three regression corollaries. Statistics-independent quartic matching structure,
scalar vertex-weight factorization, and Statistics-generic crossing-parity/pairing-weight
factorization are owned by `SecondQuantization.Common`.
-/
