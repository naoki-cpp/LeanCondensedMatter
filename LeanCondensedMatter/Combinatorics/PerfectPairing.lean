import LeanCondensedMatter.Combinatorics.PerfectPairing.Core
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.Sign
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing
import LeanCondensedMatter.Combinatorics.PerfectPairing.Bipartite
import LeanCondensedMatter.Combinatorics.PerfectPairing.Split
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.Combinatorics.PerfectPairing.ExchangeSum
import LeanCondensedMatter.Combinatorics.PerfectPairing.VertexGraph
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
the minimal bipartite matching API, scalar pairing evaluation, the generic `ζ`-weighted
pairing/permutation-sum backend, pairing-induced vertex graphs, relabeling, crossing statistics, and
the erase/insert infrastructure used by the Bloch--de Dominicis development. The four-position
enumeration is an example module and must be imported explicitly from
`PerfectPairing/Examples/Four.lean`.

The generic exchange combinatorics is statistics-agnostic: `ζ` is an arbitrary scalar, with
parity-sensitive theorems assuming `ζ * ζ = 1`. Concrete boson/fermion `Statistics` choices and
thermal operator identities remain in `SecondQuantization`.
-/
