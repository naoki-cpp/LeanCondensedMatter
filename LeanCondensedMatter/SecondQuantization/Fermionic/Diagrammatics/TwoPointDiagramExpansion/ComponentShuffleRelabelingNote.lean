import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ComponentShufflePermutation

set_option linter.style.header false

/-!
# Component-shuffle diagram-relabeling orientation

For a component shuffle, `componentShuffleSlotPermutation` is the explicit-slot form of the ambient
permutation from the common shuffle layer.  The corresponding fixed diagram uses the inverse
permutation in `relabelForComponentShuffle`, because `relabelInteractionVertices π` interprets `π`
as a map from a new slot to the old slot whose vertex label and four standard legs it inherit.

This module is intentionally theorem-free.  It fixes the convention used by the next covariance
proof relating the relabeled diagram at an unpermuted time assignment to the original diagram at the
component-shuffle-permuted time assignment.
-/
