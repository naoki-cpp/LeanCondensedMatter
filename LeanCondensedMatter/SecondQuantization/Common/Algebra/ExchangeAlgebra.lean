import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeCommutator

set_option linter.style.header false

/-!
# Exchange-algebra interface

`ExchangeAlgebra` packages the all-index CAR/CCR relations through the statistics-selected
`exchangeCommutator`. Concrete fermionic and bosonic instances remain in their own layers.
-/

namespace SecondQuantization
namespace Common

/-- Creation/annihilation operators satisfying the exchange statistics `s`. -/
class ExchangeAlgebra (s : Statistics) (Mode Config : Type*) [DecidableEq Mode] where
  /-- Annihilation operator for a mode. -/
  annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config
  /-- Creation operator for a mode. -/
  create : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config
  /-- `a_i a_j† - ζ a_j† a_i = δᵢⱼ`. -/
  annihilate_create :
    ∀ i j, exchangeCommutator s (annihilate i) (create j) = if i = j then LinearMap.id else 0
  /-- `a_i a_j - ζ a_j a_i = 0`. -/
  annihilate_annihilate : ∀ i j, exchangeCommutator s (annihilate i) (annihilate j) = 0
  /-- `a_i† a_j† - ζ a_j† a_i† = 0`. -/
  create_create : ∀ i j, exchangeCommutator s (create i) (create j) = 0

variable {s : Statistics} {Mode Config : Type*} [DecidableEq Mode] [ExchangeAlgebra s Mode Config]

/-- Generic reordering `a_i a_i† = id + ζ a_i† a_i`. -/
theorem annihilate_comp_create_self (i : Mode) :
    (ExchangeAlgebra.annihilate (s := s) (Config := Config) i).comp
        (ExchangeAlgebra.create (s := s) (Config := Config) i) =
      (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) +
        (s.zetaInt : ℂ) • ((ExchangeAlgebra.create (s := s) (Config := Config) i).comp
          (ExchangeAlgebra.annihilate (s := s) (Config := Config) i)) := by
  have hcomm := ExchangeAlgebra.annihilate_create (s := s) (Config := Config) i i
  have h := ScalarExchange.mul_eq_add_smul_mul_of_zetaCommutator_eq (s.zetaInt : ℂ)
    (by simpa [exchangeCommutator] using hcomm)
  simpa [Module.End.mul_eq_comp] using h

end Common
end SecondQuantization
