import LeanCondensedMatter.SecondQuantization.Common.ExchangeCommutator

set_option linter.style.header false

/-!
# The exchange-algebra interface, generic over the exchange statistics

Groundwork for the general (fermionic *and* bosonic) finite-temperature Bloch–de Dominicis theorem
(`notes/roadmaps/second-quantization.md`): a Bloch–de Dominicis induction needs to move a
creation/annihilation operator past another one at every step, using the *all-index* exchange
relation `a_i a_j† - ζ a_j† a_i = δᵢⱼ`, `a_i a_j - ζ a_j a_i = 0`, `a_i† a_j† - ζ a_j† a_i† = 0` —
not just the single-mode `a_i a_i† = id + ζ N_i` reordering identity
(`Fermionic/NumberOperator.lean`/`Bosonic/NumberOperator.lean`'s
`annihilate_comp_create_self`).
CAR (`ζ = -1`) and CCR (`ζ = 1`) both have exactly this shape once stated via
`Common.exchangeCommutator`, so `ExchangeAlgebra` packages it as a single interface both
statistics instantiate, letting a future `Common/BlochDeDominicis.lean` induction reference
`ExchangeAlgebra.annihilate_create`/`_annihilate_annihilate`/`_create_create` directly instead of
fermionic `anticomm_*`/bosonic `comm_*` facts.

Mirrors `Common/OccupationBasis.lean`'s architecture exactly: the interface is a `class` here in
`Common/`, and the concrete instances (`SecondQuantization.exchangeAlgebra` for the fermionic line,
which uses the plain `SecondQuantization` namespace rather than a `Fermionic` sub-namespace;
`SecondQuantization.Bosonic.exchangeAlgebra` for the bosonic line)
live in each statistics' own directory — a `Common/` file importing `Fermionic/`/`Bosonic/` would
invert the intended dependency direction (`notes/conventions.md`'s "one directory per track"
rule).

**This PR does not replace the existing public `annihilate`/`create` functions or the CAR/CCR
theorems** (`Fermionic.annihilate`/`create`, `anticomm_*`, `Bosonic.annihilate`/`create`,
`comm_*`) — the `ExchangeAlgebra` instances' fields simply reference them, so downstream files
using the statistics-specific names directly are unaffected.
-/

namespace SecondQuantization
namespace Common

/-- **The exchange-algebra interface**: an occupation-state type `Config` over modes `Mode`,
equipped with creation/annihilation operators satisfying the exchange statistics `s`'s CAR
(`s = Statistics.fermion`) or CCR (`s = Statistics.boson`) relations, stated uniformly via
`exchangeCommutator s`. -/
class ExchangeAlgebra (s : Statistics) (Mode Config : Type*) [DecidableEq Mode] where
  /-- The annihilation operator at mode `i`. -/
  annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config
  /-- The creation operator at mode `i`. -/
  create : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config
  /-- `a_i a_j† - ζ a_j† a_i = δᵢⱼ`: CAR/CCR's mixed exchange relation, all indices. -/
  annihilate_create :
    ∀ i j, exchangeCommutator s (annihilate i) (create j) = if i = j then LinearMap.id else 0
  /-- `a_i a_j - ζ a_j a_i = 0`: CAR/CCR's same-type (annihilation) exchange relation. -/
  annihilate_annihilate : ∀ i j, exchangeCommutator s (annihilate i) (annihilate j) = 0
  /-- `a_i† a_j† - ζ a_j† a_i† = 0`: CAR/CCR's same-type (creation) exchange relation. -/
  create_create : ∀ i j, exchangeCommutator s (create i) (create j) = 0

end Common
end SecondQuantization
