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

/-! ## Functoriality and linear closure -/

/-- A fixed support shift transports along any additive homomorphism of grading groups. -/
theorem CarriesShift.map {Config G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {grading : Config → G} {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    {q : G} (hA : CarriesShift grading A q) (f : G →+ H) :
    CarriesShift (f ∘ grading) A (f q) := by
  intro m n hmn
  simpa only [Function.comp_apply, map_add] using congrArg f (hA m n hmn)

/-- The zero operator satisfies every support-shift predicate. -/
theorem CarriesShift.zero {Config G : Type*} [AddCommGroup G]
    (grading : Config → G) (q : G) :
    CarriesShift grading (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) q := by
  intro m n hmn
  simp [matrixCoeff] at hmn

/-- Operators with the same support shift are closed under addition. -/
theorem CarriesShift.add {Config G : Type*} [AddCommGroup G]
    {grading : Config → G}
    {A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {q : G}
    (hA : CarriesShift grading A q) (hB : CarriesShift grading B q) :
    CarriesShift grading (A + B) q := by
  intro m n hmn
  have hcoeff : matrixCoeff (A + B) m n = matrixCoeff A m n + matrixCoeff B m n := by
    simpa only [matrixCoeffLinear_apply] using (matrixCoeffLinear m n).map_add A B
  rw [hcoeff] at hmn
  by_cases ha : matrixCoeff A m n = 0
  · exact hB m n (by simpa only [ha, zero_add] using hmn)
  · exact hA m n ha

/-- A scalar multiple preserves an operator's support shift. -/
theorem CarriesShift.smul {Config G : Type*} [AddCommGroup G]
    {grading : Config → G}
    {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {q : G}
    (hA : CarriesShift grading A q) (c : ℂ) :
    CarriesShift grading (c • A) q := by
  intro m n hmn
  have hcoeff : matrixCoeff (c • A) m n = c * matrixCoeff A m n := by
    simpa only [matrixCoeffLinear_apply, smul_eq_mul] using
      (matrixCoeffLinear m n).map_smul c A
  rw [hcoeff] at hmn
  exact hA m n (right_ne_zero_of_mul hmn)

/-- A finite sum of operators with a common support shift has that shift. -/
theorem CarriesShift.sum {Config G ι : Type*} [AddCommGroup G]
    {grading : Config → G}
    (s : Finset ι) (A : ι → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : G) (hA : ∀ i ∈ s, CarriesShift grading (A i) q) :
    CarriesShift grading (∑ i ∈ s, A i) q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using CarriesShift.zero grading q
  | @insert i s hi ih =>
      have hhead : CarriesShift grading (A i) q :=
        hA i (Finset.mem_insert_self i s)
      have htail : ∀ j ∈ s, CarriesShift grading (A j) q := by
        intro j hj
        exact hA j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sum_insert hi] using hhead.add (ih htail)

/-- If a basis vector is sent to a scalar multiple of one target basis vector with grading shift
`q`, every nonzero matrix coefficient in that column has the same grading shift. -/
theorem grading_eq_of_matrixCoeff_ne_zero_of_basisState_smul
    {Config G : Type*} [AddCommGroup G] {grading : Config → G}
    {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    {m n k : Config} {c : ℂ} {q : G}
    (hA : A (basisState n) = c • basisState k) (hmn : matrixCoeff A m n ≠ 0)
    (hk : grading k = grading n + q) :
    grading m = grading n + q := by
  have hm : m = k := by
    by_contra hmk
    apply hmn
    rw [matrixCoeff_eq_ite_of_basisState_smul hA]
    simp [hmk]
  rw [hm]
  exact hk

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
