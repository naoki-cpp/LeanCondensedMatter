import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeCommutator

set_option linter.style.header false

/-!
# The exchange-algebra interface, generic over the exchange statistics

Groundwork for the general (fermionic *and* bosonic) finite-temperature Bloch–de Dominicis theorem
(`notes/roadmaps/second-quantization.md`): a Bloch–de Dominicis induction needs to move a
creation/annihilation operator past another one at every step, using the *all-index* exchange
relation `a_i a_j† - ζ a_j† a_i = δᵢⱼ`, `a_i a_j - ζ a_j a_i = 0`, `a_i† a_j† - ζ a_j† a_i† = 0` —
not just the single-mode `a_i a_i† = id + ζ N_i` reordering identity
(`Fermionic/Algebra/NumberOperator.lean`/`Bosonic/Algebra/NumberOperator.lean`'s
`annihilate_comp_create_self`).
CAR (`ζ = -1`) and CCR (`ζ = 1`) both have exactly this shape once stated via
`Common.exchangeCommutator`, so `ExchangeAlgebra` packages it as a single interface both
statistics instantiate, letting the common thermal induction reference
`ExchangeAlgebra.annihilate_create`/`_annihilate_annihilate`/`_create_create` directly instead of
fermionic `anticomm_*` or bosonic `comm_*` facts.

The architecture mirrors `Common/Algebra/OccupationBasis.lean`: the interface is a `class` in
`Common/`, and the concrete instances (`SecondQuantization.Fermionic.exchangeAlgebra` and
`SecondQuantization.Bosonic.exchangeAlgebra`) live in each statistics-specific directory. A
`Common/` file importing `Fermionic/` or `Bosonic/` would invert the intended dependency direction
documented in `notes/conventions.md`.

The interface does not replace the existing public `annihilate`/`create` functions or the CAR/CCR
theorems (`Fermionic.annihilate`/`create`, `anticomm_*`, `Bosonic.annihilate`/`create`, `comm_*`).
The `ExchangeAlgebra` instances' fields simply reference them, so downstream files using the
statistics-specific names directly remain on those APIs.
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

variable {s : Statistics} {Mode Config : Type*} [DecidableEq Mode] [ExchangeAlgebra s Mode Config]

/-- **`[a_i, a_i†]_ζ = id`, for any statistics instantiating `ExchangeAlgebra`**: the `i = j` case
of `annihilate_create`. The fermionic and bosonic `NumberOperator` specializations obtain their
corresponding self-mode exchange identity from this statistics-generic statement. -/
theorem exchangeCommutator_annihilate_create_self (i : Mode) :
    exchangeCommutator s (ExchangeAlgebra.annihilate (s := s) (Config := Config) i)
      (ExchangeAlgebra.create (s := s) (Config := Config) i) =
      (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
  have h := ExchangeAlgebra.annihilate_create (s := s) (Config := Config) i i
  rwa [if_pos rfl] at h

/-- **`a_i a_i† = id + ζ•N_i`, for any statistics instantiating `ExchangeAlgebra`**, from
`exchangeCommutator_annihilate_create_self` via `comp_eq_id_add_of_zetaCommutator_eq_id`. Its
fermionic specialization is `c_i c_i† = id - N_i` and its bosonic specialization is
`a_i a_i† = id + N_i`. -/
theorem annihilate_comp_create_self (i : Mode) :
    (ExchangeAlgebra.annihilate (s := s) (Config := Config) i).comp
        (ExchangeAlgebra.create (s := s) (Config := Config) i) =
      (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) +
        (s.zetaInt : ℂ) • ((ExchangeAlgebra.create (s := s) (Config := Config) i).comp
          (ExchangeAlgebra.annihilate (s := s) (Config := Config) i)) :=
  comp_eq_id_add_of_zetaCommutator_eq_id (s.zetaInt : ℂ)
    (exchangeCommutator_annihilate_create_self i)

end Common
end SecondQuantization
