import LeanCondensedMatter.Combinatorics.PerfectPairing.Core
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZero
import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingEraseZero
import LeanCondensedMatter.Combinatorics.PerfectPairing.InsertFirstPair
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Perfect pairings of ordered finite positions

Importing this module provides the core pairing type, normalized endpoints, relabeling, crossing
statistics, and the first-pair erase/insert recursion used by the Bloch--de Dominicis development.
The four-position enumeration is an example module and must be imported explicitly from
`PerfectPairing/Examples/Four.lean`.

The implementation is purely combinatorial: statistics-dependent exchange weights and thermal
operator identities remain in `SecondQuantization`.
-/
