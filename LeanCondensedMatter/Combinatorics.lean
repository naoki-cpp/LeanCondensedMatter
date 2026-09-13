import LeanCondensedMatter.Combinatorics.FiniteIndex
import LeanCondensedMatter.Combinatorics.SumEquivPartition
import LeanCondensedMatter.Combinatorics.BinaryShuffle
import LeanCondensedMatter.Combinatorics.BinaryShuffleSlotEquiv
import LeanCondensedMatter.Combinatorics.BinaryShuffleSlots
import LeanCondensedMatter.Combinatorics.FamilySlotShuffle
import LeanCondensedMatter.Combinatorics.FamilySlotShuffleDecomposition
import LeanCondensedMatter.Combinatorics.FinpartitionOrderShuffle
import LeanCondensedMatter.Combinatorics.IncidenceAlgebra
import LeanCondensedMatter.Combinatorics.SetPartition
import LeanCondensedMatter.Combinatorics.Cumulant
import LeanCondensedMatter.Combinatorics.PerfectPairing
import LeanCondensedMatter.Combinatorics.SubsetSplit
import LeanCondensedMatter.Combinatorics.InvolutionCard

set_option linter.style.header false

/-!
# Combinatorics

Public entry point for the project's pure finite combinatorics. The implementation is organized
around finite-index operations, shuffles, finite partitions, set partitions and cumulants, and
perfect pairings.

The public import surface uses package-level routing modules where the corresponding directory is a
public boundary. Internal helper directories remain narrow imports.

The exchange-weighted permutation theory is owned by the separate top-level
`LeanCondensedMatter.Permutation` module.
-/
