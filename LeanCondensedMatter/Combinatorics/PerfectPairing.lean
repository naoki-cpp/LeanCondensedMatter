import LeanCondensedMatter.Combinatorics.PerfectPairing.Core
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.Sign
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing
import LeanCondensedMatter.Combinatorics.PerfectPairing.Bipartite
import LeanCondensedMatter.Combinatorics.PerfectPairing.Split
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.Combinatorics.PerfectPairing.VertexGraph
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction
import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZero
import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingEraseZero
import LeanCondensedMatter.Combinatorics.PerfectPairing.InsertFirstPair
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Perfect pairings of ordered finite positions

Importing this module provides the core pairing type, normalized endpoints, pairing presentations,
the minimal bipartite matching API, scalar pairing evaluation, pairing-induced vertex graphs,
partner-invariant restriction and reindexing, relabeling, crossing statistics, and the erase/insert
infrastructure used by the Bloch--de Dominicis development. The four-position enumeration and the
exchange-weighted sum backend are separate modules and must be imported explicitly when needed.

This entry point stays purely at the pairing-structure level. The separate `Permutation.PairingBridge`
module owns only the crossing-weighted pairing sum and its parity-sensitive bridge to the generic
`ζ`-weighted permutation backend.
-/
