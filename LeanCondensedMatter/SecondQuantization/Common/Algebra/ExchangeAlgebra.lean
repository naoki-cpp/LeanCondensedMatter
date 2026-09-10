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

/-- Same-mode mixed exchange relation `[a_i,a_i†]_ζ = id`. -/
theorem exchangeCommutator_annihilate_create_self (i : Mode) :
    exchangeCommutator s (ExchangeAlgebra.annihilate (s := s) (Config := Config) i)
      (ExchangeAlgebra.create (s := s) (Config := Config) i) =
      (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
  have h := ExchangeAlgebra.annihilate_create (s := s) (Config := Config) i i
  rwa [if_pos rfl] at h

/-- Reverse mixed exchange relation `[a_i†,a_j]_ζ = -ζ δᵢⱼ`. -/
theorem exchangeCommutator_create_annihilate (i j : Mode) :
    exchangeCommutator s (ExchangeAlgebra.create (s := s) (Config := Config) i)
      (ExchangeAlgebra.annihilate (s := s) (Config := Config) j) =
      if i = j then (-(s.zetaInt : ℂ)) •
        (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) else 0 := by
  have hζ : (s.zetaInt : ℂ) * (s.zetaInt : ℂ) = 1 := by
    exact_mod_cast s.zeta_sq
  calc
    exchangeCommutator s (ExchangeAlgebra.create (s := s) (Config := Config) i)
        (ExchangeAlgebra.annihilate (s := s) (Config := Config) j) =
      (-(s.zetaInt : ℂ)) • exchangeCommutator s
        (ExchangeAlgebra.annihilate (s := s) (Config := Config) j)
        (ExchangeAlgebra.create (s := s) (Config := Config) i) := by
          simpa [exchangeCommutator] using
            (LinearMap.zetaCommutator_swap_of_sq_eq_one (s.zetaInt : ℂ) hζ
              (ExchangeAlgebra.annihilate (s := s) (Config := Config) j)
              (ExchangeAlgebra.create (s := s) (Config := Config) i))
    _ = if i = j then (-(s.zetaInt : ℂ)) •
        (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) else 0 := by
      rw [ExchangeAlgebra.annihilate_create]
      by_cases h : i = j
      · subst j
        simp
      · simp [h, Ne.symm h]

/-- Generic reordering `a_i a_i† = id + ζ a_i† a_i`. -/
theorem annihilate_comp_create_self (i : Mode) :
    (ExchangeAlgebra.annihilate (s := s) (Config := Config) i).comp
        (ExchangeAlgebra.create (s := s) (Config := Config) i) =
      (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) +
        (s.zetaInt : ℂ) • ((ExchangeAlgebra.create (s := s) (Config := Config) i).comp
          (ExchangeAlgebra.annihilate (s := s) (Config := Config) i)) := by
  apply LinearMap.comp_eq_add_smul_comp_of_zetaCommutator_eq (s.zetaInt : ℂ)
  simpa [exchangeCommutator] using (exchangeCommutator_annihilate_create_self i)

end Common
end SecondQuantization
