import LeanCondensedMatter.Analysis.DiscreteLattice
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationCommutator
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# Fermionic second-quantized discrete lattice currents

One-body lattice states, matrix units, hopping operators, and the local commutator identity are
defined upstream in `Analysis.DiscreteLattice`. This module realizes those operators on the
fermionic Fock space using `dGamma` and proves the many-body continuity equation.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic
namespace Lattice

attribute [local instance 100] LieRing.ofAssociativeRing

variable {Site : Type*} [DecidableEq Site]

/-- The many-particle hopping Hamiltonian obtained by second-quantizing the one-particle hopping
operator. -/
noncomputable def hoppingHamiltonian (K : LocallyFiniteHopping Site) :
    AlgebraicFock ((Site →₀ ℂ)) →ₗ[ℂ]
      AlgebraicFock ((Site →₀ ℂ)) :=
  AlgebraicFock.dGamma ((Site →₀ ℂ)) K.operator

/-- Many-particle charge localized at one lattice site. -/
noncomputable def siteChargeDensity (q : ℂ) (x : Site) :
    AlgebraicFock ((Site →₀ ℂ)) →ₗ[ℂ]
      AlgebraicFock ((Site →₀ ℂ)) :=
  q • AlgebraicFock.dGamma ((Site →₀ ℂ)) (siteProjector x)

/-- The oriented many-particle bond current. The convention is

`J_(x→y) = (i q / ℏ) dΓ(h_xy |x⟩⟨y| - h_yx |y⟩⟨x|)`.
-/
noncomputable def bondCurrent (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (x y : Site) :
    AlgebraicFock ((Site →₀ ℂ)) →ₗ[ℂ]
      AlgebraicFock ((Site →₀ ℂ)) :=
  ((Complex.I * q) / ℏ) • AlgebraicFock.dGamma ((Site →₀ ℂ)) (K.bondOperator x y)

/-- Bond current is antisymmetric under orientation reversal. -/
theorem bondCurrent_swap (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (x y : Site) :
    bondCurrent ℏ q K y x = -bondCurrent ℏ q K x y := by
  unfold bondCurrent
  rw [K.bondOperator_swap]
  have hneg :
      AlgebraicFock.dGamma ((Site →₀ ℂ)) (-K.bondOperator x y) =
        -AlgebraicFock.dGamma ((Site →₀ ℂ)) (K.bondOperator x y) := by
    change
      AlgebraicFock.dGammaLinear ((Site →₀ ℂ)) (-K.bondOperator x y) =
        -AlgebraicFock.dGammaLinear ((Site →₀ ℂ)) (K.bondOperator x y)
    exact map_neg (AlgebraicFock.dGammaLinear ((Site →₀ ℂ))) (K.bondOperator x y)
  rw [hneg]
  exact smul_neg _ _

/-- The algebraic discrete continuity equation on an arbitrary locally finite lattice. -/
theorem discrete_continuity (ℏ q : ℂ)
    (K : LocallyFiniteHopping Site) (x : Site) :
    (Complex.I / ℏ) •
          ⁅hoppingHamiltonian K, siteChargeDensity q x⁆ +
        ∑ y ∈ K.incident x, bondCurrent ℏ q K x y = 0 := by
  have hheisenberg :
      (Complex.I / ℏ) •
          ⁅hoppingHamiltonian K, siteChargeDensity q x⁆ =
        -∑ y ∈ K.incident x, bondCurrent ℏ q K x y := by
    unfold hoppingHamiltonian siteChargeDensity
    rw [lie_smul]
    rw [AlgebraicFock.dGamma_lie]
    rw [K.lie_siteProjector]
    have hdGamma :
        AlgebraicFock.dGamma ((Site →₀ ℂ)) (-∑ y ∈ K.incident x, K.bondOperator x y) =
          -∑ y ∈ K.incident x,
            AlgebraicFock.dGamma ((Site →₀ ℂ)) (K.bondOperator x y) := by
      change
        AlgebraicFock.dGammaLinear ((Site →₀ ℂ)) (-∑ y ∈ K.incident x, K.bondOperator x y) =
          -∑ y ∈ K.incident x,
            AlgebraicFock.dGammaLinear ((Site →₀ ℂ)) (K.bondOperator x y)
      rw [map_neg, map_sum]
    rw [hdGamma]
    unfold bondCurrent
    simp only [smul_smul, smul_neg, Finset.smul_sum]
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    ring
  rw [hheisenberg]
  abel

end Lattice
end Fermionic
end SecondQuantization
