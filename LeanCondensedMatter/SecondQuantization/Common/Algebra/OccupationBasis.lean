import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

set_option linter.style.header false

/-!
# The occupation-basis interface

`OccupationBasis` captures the statistics-independent structure shared by fermionic and bosonic
occupation descriptions: a vacuum configuration, a per-mode occupation number, vanishing vacuum
occupation, finite support, and extensionality from the occupation data. These assumptions define the
common total `particleNumber` grading.

The concrete configuration types remain distinct. Fermions use finite subsets of modes with
occupations in `{0, 1}`, while bosons use finitely supported `ℕ`-valued occupations. Each
statistics-specific algebra supplies its own `OccupationBasis` instance.
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

/-- **The total particle-number grade** of an occupation-basis state. The sum is taken over the
finite support supplied by `OccupationBasis`, so the definition works for arbitrary mode types
without a `Fintype Mode` assumption. -/
noncomputable def particleNumber {Mode Config : Type*} [OccupationBasis Mode Config]
    (n : Config) : ℕ :=
  (OccupationBasis.finiteSupport (Mode := Mode) (Config := Config) n).toFinset.sum
    (OccupationBasis.occupation (Mode := Mode) (Config := Config) n)

@[simp]
theorem particleNumber_vacuum {Mode Config : Type*} [OccupationBasis Mode Config] :
    particleNumber (Mode := Mode) (Config := Config)
      (OccupationBasis.vacuum (Mode := Mode) (Config := Config)) = 0 := by
  classical
  simp [particleNumber, OccupationBasis.occupation_vacuum]

end Common
end SecondQuantization
