import LeanCondensedMatter.Combinatorics.PerfectPairing.Core
import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZero
import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingEraseZero
import LeanCondensedMatter.Combinatorics.PerfectPairing.InsertFirstPair
import LeanCondensedMatter.Combinatorics.PerfectPairing.FourPositions
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Pairings for the finite-temperature Bloch--de Dominicis theorem

The target of this project is the finite-temperature Bloch--de Dominicis factorization of
free/quasifree Gibbs expectations, not the vacuum-expectation Wick theorem or an arbitrary
interacting thermal state.  The namespace and module name make that distinction explicit even
though the finite pairing combinatorics itself does not depend on a temperature parameter.

Importing this module brings in the whole `PerfectPairing/` subdirectory:
- `PerfectPairing/Core.lean`: the `Pairing n` type, its finite enumeration, and normalized
  `pairs`.
- `PerfectPairing/EraseZero.lean`: `Pairing.eraseZeroPair`, removing position `0` and its
  partner.
- `PerfectPairing/Crossing.lean`: `Crosses`, `crossingCount`, `firstPair`.
- `PerfectPairing/CrossingEraseZero.lean`: `crossingCount`'s split along
  `firstPair`/`eraseZeroPair`.
- `PerfectPairing/InsertFirstPair.lean`: `Pairing.insertFirstPair` and the `equivSigma`
  decomposition.
- `PerfectPairing/FourPositions.lean`: the three perfect pairings of four positions, a finite
  example.
- `PerfectPairing/Relabel.lean`: `Pairing.relabel`/`Pairing.relabelEquiv`, transporting a pairing
  along an ambient relabeling of its positions.

**File location vs. namespace**: being purely combinatorial, these files live in the general-math
`Combinatorics/` layer (with `Combinatorics/Common/`), upstream of all of `SecondQuantization/`.
The declarations keep their original `SecondQuantization.Common.BlochDeDominicis` namespace (a
namespace migration, if ever wanted, is separate work).

This subdirectory is purely combinatorial and has no `Statistics`/`ℂ` dependency at all: it defines
neither operator-valued time ordering, thermal contractions, thermal expectations, the
exchange-statistics weight, nor the Bloch--de Dominicis factorization theorem itself, and it
imports neither statistics-specific implementation directory. The statistics-dependent exchange
weight `ζ ^ crossingCount` itself — `ζ = +1` for bosons, `ζ = -1` for fermions — is defined
separately, in `Common/BlochDeDominicis/PairingWeight.lean`.
-/
