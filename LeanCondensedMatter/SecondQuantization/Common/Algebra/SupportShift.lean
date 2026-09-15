import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock

set_option linter.style.header false

/-!
# Fixed support shifts of algebraic Fock-space operators

`CarriesShift grading A q` records a support-level selection rule: every nonzero matrix coefficient
of `A` connects basis states whose values under the additive grading `grading` differ by the fixed
shift `q`. The grading may take values in any additive commutative group, so the same notion covers
integer particle-number charge and real energy shifts.

Fixed shifts compose additively under operator composition. A nonzero shift also forces every
diagonal matrix coefficient to vanish.
-/

namespace SecondQuantization
namespace Common

/-- `A` carries fixed shift `q` with respect to an additive grading when every nonzero matrix
coefficient `Aₘₙ` satisfies `grading m = grading n + q`. -/
def CarriesShift {Config G : Type*} [AddCommGroup G] (grading : Config → G)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (q : G) : Prop :=
  ∀ m n, matrixCoeff A m n ≠ 0 → grading m = grading n + q

/-- Fixed support shifts compose additively under `LinearMap.comp`. -/
theorem CarriesShift.comp {Config G : Type*} [AddCommGroup G] {grading : Config → G}
    {A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {qA qB : G}
    (hA : CarriesShift grading A qA) (hB : CarriesShift grading B qB) :
    CarriesShift grading (A.comp B) (qA + qB) := by
  intro m n hmn
  by_contra hshift
  apply hmn
  rw [matrixCoeff_comp_support]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hAk : matrixCoeff A m k = 0
  · simp [hAk]
  · by_cases hBk : matrixCoeff B k n = 0
    · simp [hBk]
    · exfalso
      apply hshift
      calc
        grading m = grading k + qA := hA m k hAk
        _ = (grading n + qB) + qA := by rw [hB k n hBk]
        _ = grading n + (qA + qB) := by ac_rfl

/-- An operator carrying a nonzero shift has vanishing diagonal matrix coefficients. -/
theorem diagonalCoeff_eq_zero_of_carriesShift {Config G : Type*} [AddCommGroup G]
    {grading : Config → G} {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {q : G}
    (hA : CarriesShift grading A q) (hq : q ≠ 0) (n : Config) :
    diagonalCoeff A n = 0 := by
  unfold diagonalCoeff
  by_contra h
  have hshift := hA n n h
  have hEq : grading n + q = grading n + 0 := by simpa using hshift.symm
  exact hq (add_left_cancel hEq)

end Common
end SecondQuantization
