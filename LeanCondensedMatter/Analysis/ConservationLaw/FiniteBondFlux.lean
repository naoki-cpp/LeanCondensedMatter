import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# Finite oriented bond flux

For a finite set of sites, an antisymmetric bond flux has vanishing total
outflow. Consequently, a site source with nonzero total cannot be represented
as the divergence of an antisymmetric bond flux on a closed finite lattice.

This purely algebraic obstruction does not assume a particular current operator,
particle statistics, translation symmetry, or boundary model.
-/

namespace ConservationLaw

open scoped BigOperators

variable {Site Obs : Type*}
variable [Fintype Site] [AddCommGroup Obs] [Module ℂ Obs]

/-- Total outflow vanishes for any antisymmetric oriented bond flux on a finite
closed set of sites. This statement uses characteristic zero. -/
theorem sum_antisymmetric_bondFlux_eq_zero
    (J : Site → Site → Obs) (hantisym : ∀ x y, J x y = -J y x) :
    (∑ x : Site, ∑ y : Site, J x y) = 0 := by
  classical
  let S : Obs := ∑ x : Site, ∑ y : Site, J x y
  have hswap : S = -S := by
    calc
      S = ∑ x : Site, ∑ y : Site, J y x := by
        dsimp [S]
        exact Finset.sum_comm
      _ = ∑ x : Site, ∑ y : Site, -J x y := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact hantisym y x
      _ = -S := by
        simp [S, Finset.sum_neg_distrib]
  have htwo : (2 : ℂ) • S = 0 := by
    calc
      (2 : ℂ) • S = S + S := by module
      _ = 0 := by rw [hswap]; simp
  have hS : S = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact hS

/-- Nonzero total source on a finite closed lattice cannot be written as the
outflow of a pairwise antisymmetric bond current. -/
theorem nonzero_totalSource_not_bondFlux
    (source : Site → Obs) (hsource : (∑ x : Site, source x) ≠ 0) :
    ¬ ∃ J : Site → Site → Obs,
      (∀ x y, J x y = -J y x) ∧
        (∀ x, source x = ∑ y : Site, J x y) := by
  rintro ⟨J, hantisym, hbalance⟩
  apply hsource
  calc
    (∑ x : Site, source x) =
        ∑ x : Site, ∑ y : Site, J x y := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hbalance x
    _ = 0 := sum_antisymmetric_bondFlux_eq_zero J hantisym

end ConservationLaw
