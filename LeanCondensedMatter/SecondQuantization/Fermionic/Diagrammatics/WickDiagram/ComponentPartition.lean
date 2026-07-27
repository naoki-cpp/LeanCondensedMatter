import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentPartition
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Connected

set_option linter.style.header false

/-!
# Fermionic quartic-diagram component partitions

This module specializes the label-generic connected-component partition to fermionic quartic
vertex labels while preserving the existing public names.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

noncomputable section

abbrev QuarticWickDiagram.componentBlock {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (v : ↥S) : Finset (Fin N) :=
  Common.QuarticDiagram.componentBlock d v

theorem QuarticWickDiagram.mem_componentBlock {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (v : ↥S) {x : Fin N} :
    x ∈ d.componentBlock v ↔ ∃ hx : x ∈ S, d.vertexGraph.Reachable ⟨x, hx⟩ v :=
  Common.QuarticDiagram.mem_componentBlock d v

@[simp]
theorem QuarticWickDiagram.self_mem_componentBlock {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (v : ↥S) : (v : Fin N) ∈ d.componentBlock v :=
  Common.QuarticDiagram.self_mem_componentBlock d v

theorem QuarticWickDiagram.componentBlock_eq_of_reachable {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {v w : ↥S} (h : d.vertexGraph.Reachable v w) :
    d.componentBlock v = d.componentBlock w :=
  Common.QuarticDiagram.componentBlock_eq_of_reachable d h

theorem QuarticWickDiagram.componentBlock_disjoint_of_not_reachable {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {v w : ↥S} (h : ¬ d.vertexGraph.Reachable v w) :
    Disjoint (d.componentBlock v) (d.componentBlock w) :=
  Common.QuarticDiagram.componentBlock_disjoint_of_not_reachable d h

abbrev QuarticWickDiagram.componentPartition {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) : Finpartition S :=
  Common.QuarticDiagram.componentPartition d

theorem QuarticWickDiagram.componentBlock_mem_componentPartition {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (v : ↥S) :
    d.componentBlock v ∈ d.componentPartition.parts :=
  Common.QuarticDiagram.componentBlock_mem_componentPartition d v

theorem QuarticWickDiagram.exists_componentBlock_eq_of_mem {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : ∃ v : ↥S, d.componentBlock v = B :=
  Common.QuarticDiagram.exists_componentBlock_eq_of_mem d hB

end

end SecondQuantization
