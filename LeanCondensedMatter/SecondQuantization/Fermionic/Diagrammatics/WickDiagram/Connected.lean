import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Connected
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram

set_option linter.style.header false

/-!
# Fermionic quartic Wick diagram connectivity

The connectivity API specializes the label-generic quartic-diagram construction to fermionic
quartic vertex labels while preserving the existing public names.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} {N : ℕ}

noncomputable section

/-- The graph connecting distinct vertices whose legs are paired. -/
abbrev QuarticWickDiagram.vertexGraph {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) : SimpleGraph (↥S) :=
  Common.QuarticDiagram.vertexGraph d

/-- A quartic Wick diagram is connected when its vertex graph is preconnected and `S` is nonempty. -/
abbrev QuarticWickDiagram.IsConnected {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) : Prop :=
  Common.QuarticDiagram.IsConnected d

/-- The subtype of connected quartic Wick diagrams on vertex set `S`. -/
abbrev ConnectedQuarticWickDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) : Type _ :=
  Common.ConnectedQuarticDiagram (QuarticVertexLabel Mode) N S

/-- Connected quartic Wick diagrams form a finite type whenever the underlying mode type is finite. -/
noncomputable instance ConnectedQuarticWickDiagram.instFintype [DecidableEq Mode] [Fintype Mode]
    {S : Finset (Fin N)} : Fintype (ConnectedQuarticWickDiagram Mode N S) :=
  Fintype.ofInjective (fun d => d.1) fun _ _ h => Subtype.ext h

end

end Fermionic
end SecondQuantization
