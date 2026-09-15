import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentVertexProduct
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.FieldLabel
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction

set_option linter.style.header false

/-!
# Fermionic two-point Wick diagrams

This module specializes the mixed one-leg/four-leg diagram data to a fermionic two-point function.
The two external labels record an annihilation field and a creation field; their imaginary times are
parameters of the future amplitude rather than part of the finite diagram enumeration. The full
external-plus-interaction component partition, vacuum/external component restrictions,
componentwise vertex and normalized-pair product decompositions, restricted-pair equivalences, and
restricted pair-orientation dichotomies are inherited from the statistics-independent layer.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} {N : ℕ}

/-- A fermionic two-point diagram with one annihilation leg, one creation leg, and quartic
interaction vertices. -/
abbrev TwoPointWickDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Common.TwoPointDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) N S

/-- Construct a two-point Wick diagram with the canonical annihilation/creation external ordering. -/
def TwoPointWickDiagram.ofModes {S : Finset (Fin N)} (i j : Mode)
    (vertexLabel : ↥S → QuarticVertexLabel Mode) (pairing : Combinatorics.Pairing (2 * S.card + 1)) :
    TwoPointWickDiagram Mode N S where
  externalLabel := twoPointExternalLabels i j
  vertexLabel := vertexLabel
  pairing := pairing

/-- A fermionic two-point diagram with all vacuum components removed. -/
abbrev VacuumFreeTwoPointWickDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Common.VacuumFreeTwoPointDiagram
    (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) N S

/-- A fermionic two-point diagram whose two external vertices lie in the same connected component
and which has no vacuum component. -/
abbrev ConnectedTwoPointWickDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Common.ExternallyConnectedTwoPointDiagram
    (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) N S

end Fermionic
end SecondQuantization
