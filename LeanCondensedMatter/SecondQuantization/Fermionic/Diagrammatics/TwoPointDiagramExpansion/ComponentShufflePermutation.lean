import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentShufflePermutation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabel

set_option linter.style.header false

/-!
# Component-shuffle permutations for fixed fermionic two-point diagrams

The Common layer owns the ambient component-shuffle permutation, its transport from `Fin univ.card`
to the explicit interaction-slot type `Fin n`, and the corresponding standard two-point diagram
relabeling. This file lifts that relabeling through the fixed fermionic external-label subtype.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Lift the Common component-shuffle relabeling through the fixed external-label subtype. -/
noncomputable def FixedExternalTwoPointWickDiagram.relabelForComponentShuffle
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (shuffle : d.1.ComponentInteractionShuffle) : FixedExternalTwoPointWickDiagram Mode n i j :=
  ⟨d.1.relabelForComponentShuffle shuffle, by simpa using d.2⟩

omit [LinearOrder Mode] [Fintype Mode] in
/-- The fixed-external lift is exactly the existing interaction-relabel lift at the Common-owned
component-shuffle slot permutation. -/
theorem FixedExternalTwoPointWickDiagram.relabelForComponentShuffle_eq_relabelInteractionVertices
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (shuffle : d.1.ComponentInteractionShuffle) :
    d.relabelForComponentShuffle shuffle =
      d.relabelInteractionVertices (d.1.componentShuffleSlotPermutation shuffle).symm := by
  apply Subtype.ext
  rfl

end Fermionic
end SecondQuantization
