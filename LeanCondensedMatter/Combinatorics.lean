import LeanCondensedMatter.Combinatorics.FiniteIndex
import LeanCondensedMatter.Combinatorics.FiniteSumModEq
import LeanCondensedMatter.Combinatorics.Shuffle.SlotShuffle
import LeanCondensedMatter.Combinatorics.Shuffle.BinaryShuffle
import LeanCondensedMatter.Combinatorics.Shuffle.BinaryShuffleSlots
import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffle
import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffleInversions
import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffleSign
import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffleDecomposition
import LeanCondensedMatter.Combinatorics.Shuffle.FinpartitionOrderShuffle
import LeanCondensedMatter.Combinatorics.IncidenceAlgebra.Mobius
import LeanCondensedMatter.Combinatorics.SetPartition
import LeanCondensedMatter.Combinatorics.Cumulant
import LeanCondensedMatter.Combinatorics.PerfectPairing

set_option linter.style.header false

/-!
# Combinatorics

Finite combinatorics used throughout the project: finite-index operations, shuffles, finite and
graph-component partitions, incidence algebra, cumulants, perfect pairings, subset decompositions,
and
involution-cardinality results.

Exchange-weighted permutation theory is developed separately in `LeanCondensedMatter.Permutation`.
-/
