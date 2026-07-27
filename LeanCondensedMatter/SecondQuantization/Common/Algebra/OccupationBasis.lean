import Mathlib.Data.Set.Finite.Basic

set_option linter.style.header false

/-!
# The occupation-basis interface, generic over the concrete occupation-state type

Shared architectural vocabulary for Track D's fermionic and bosonic lines
(`notes/roadmaps/second-quantization.md`): both lines represent a Fock-space basis vector by a
concrete occupation state (`FermionOccupation Mode := Finset Mode` for fermions, `Occupation Mode
:= Mode →₀ ℕ` for bosons) together with a per-mode occupation number extracted from it
(`i ∈ n ↦ 1`/`0` for fermions, `n i` directly for bosons). `OccupationBasis` packages just that
common shape — a `vacuum`, an `occupation : Config → Mode → ℕ` reading off each mode's particle
count, and the basic facts (`vacuum` has none, each state has finite support, the reading is
faithful) — without unifying `Config` itself: fermionic and bosonic occupation-state types stay
genuinely different (`Finset Mode` vs. `Mode →₀ ℕ`, since Pauli exclusion caps the former at
`0`/`1`), each supplying its own instance of this structure.

The concrete instances (`SecondQuantization.occupationBasis` for the fermionic line, which uses
the plain `SecondQuantization` namespace rather than a `Fermionic` sub-namespace;
`SecondQuantization.Bosonic.occupationBasis` for the bosonic line) live in each statistics' own
directory, not here, since a `Common/` file importing `Fermionic/`/`Bosonic/` would invert the
intended dependency direction (`notes/conventions.md`'s "one directory per track" rule:
statistics-specific code depends on `Common/`, not the reverse).
-/

namespace SecondQuantization
namespace Common

/-- **The occupation-basis interface**: a Fock-space basis type `Config`, together with a
`vacuum` state and a per-mode occupation-number reading `occupation : Config → Mode → ℕ`, subject
to the physically expected constraints — the vacuum has no particles anywhere, every state has
only finitely many occupied modes, and the reading determines the state. A `class` (not a plain
`structure`) so each statistics' concrete instance is found by typeclass resolution once `Mode`
and its `Config` are fixed, rather than needing to be threaded explicitly. -/
class OccupationBasis (Mode Config : Type*) where
  /-- The zero-particle state. -/
  vacuum : Config
  /-- The occupation number of mode `i` in state `n`. -/
  occupation : Config → Mode → ℕ
  /-- The vacuum has no particles in any mode. -/
  occupation_vacuum : ∀ i, occupation vacuum i = 0
  /-- Every occupation state has only finitely many occupied modes. -/
  finiteSupport : ∀ n, Set.Finite {i | occupation n i ≠ 0}
  /-- The occupation-number reading determines the state. -/
  ext : ∀ {m n}, (∀ i, occupation m i = occupation n i) → m = n

end Common
end SecondQuantization
