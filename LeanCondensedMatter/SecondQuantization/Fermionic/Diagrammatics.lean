import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointWickDiagram
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonConnectedDiagramExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonLinkedClusterTheorem
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonLinkedClusterLowOrder

set_option linter.style.header false

/-!
# Fermionic diagrammatics

Quartic interaction vertices, local-leg semantics, ordered Wick diagrams and amplitudes, and their
connected-component factorization; the two-point external-leg foundation and perturbative diagram
expansion; the Dyson diagram expansion, connected-diagram formula for Dyson vertex cumulants, the
general algebraic Dyson Linked Cluster Theorem, and its explicit low-order regression corollaries.
Statistics-independent quartic and two-point diagram structure is owned by
`SecondQuantization.Common`.
-/
