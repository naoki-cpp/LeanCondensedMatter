import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing

set_option linter.style.header false

/-!
# The three perfect pairings of four positions

Finite examples, not general API: the adjacent/crossing/nested pairings of `Fin 4` and their
crossing counts, matching the sign pattern the four-point Bloch–de Dominicis formula uses.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- The adjacent four-position pairing `(0,1)(2,3)`. -/
def pairingAdjacent : Pairing 2 :=
  Pairing.ofPartner (Equiv.swap 0 1 * Equiv.swap 2 3) (by decide)

/-- The crossing four-position pairing `(0,2)(1,3)`. -/
def pairingCrossing : Pairing 2 :=
  Pairing.ofPartner (Equiv.swap 0 2 * Equiv.swap 1 3) (by decide)

/-- The nested four-position pairing `(0,3)(1,2)`. -/
def pairingNested : Pairing 2 :=
  Pairing.ofPartner (Equiv.swap 0 3 * Equiv.swap 1 2) (by decide)

/-- There are exactly three perfect pairings of four ordered positions, stated as a `Finset`
equality so the result is independent of any enumeration order. -/
theorem allPairings_two :
    allPairings 2 = {pairingAdjacent, pairingCrossing, pairingNested} := by
  decide

@[simp]
theorem crossingCount_pairingAdjacent : pairingAdjacent.crossingCount = 0 := by
  decide

@[simp]
theorem crossingCount_pairingCrossing : pairingCrossing.crossingCount = 1 := by
  decide

@[simp]
theorem crossingCount_pairingNested : pairingNested.crossingCount = 0 := by
  decide

end BlochDeDominicis
end Common
end SecondQuantization
