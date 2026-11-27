import LeanCondensedMatter.Analysis.Algebra.FinsuppCoordinates

set_option linter.style.header false

/-!
# Fixed grading shifts of linear maps on free modules

A nonzero coordinate of the image of a basis vector can connect only grades
differing by a prescribed additive shift. No finiteness assumption on the
index type is needed.
-/

namespace Finsupp

variable {R Config G H ι : Type*} [CommSemiring R] [AddCommGroup G]

/-- Every nonzero coordinate connects indices whose grades differ by `q`. -/
def CarriesShift (grading : Config → G)
    (A : (Config →₀ R) →ₗ[R] (Config →₀ R)) (q : G) : Prop :=
  ∀ m n, A (Finsupp.single n 1) m ≠ 0 → grading m = grading n + q

variable {grading : Config → G}
variable {A B : (Config →₀ R) →ₗ[R] (Config →₀ R)} {q qA qB : G}

/-- A fixed support shift transports along an additive homomorphism. -/
theorem CarriesShift.map [AddCommGroup H]
    (hA : CarriesShift grading A q) (f : G →+ H) :
    CarriesShift (f ∘ grading) A (f q) := by
  intro m n hmn
  simpa only [Function.comp_apply, map_add] using congrArg f (hA m n hmn)

/-- The zero map carries every shift. -/
theorem CarriesShift.zero (grading : Config → G) (q : G) :
    CarriesShift grading (0 : (Config →₀ R) →ₗ[R] (Config →₀ R)) q := by
  intro m n hmn
  simp at hmn

/-- Maps with the same shift are closed under addition. -/
theorem CarriesShift.add (hA : CarriesShift grading A q) (hB : CarriesShift grading B q) :
    CarriesShift grading (A + B) q := by
  intro m n hmn
  by_cases ha : A (Finsupp.single n 1) m = 0
  · exact hB m n (by simpa [ha] using hmn)
  · exact hA m n ha

/-- Scalar multiplication preserves the shift. -/
theorem CarriesShift.smul (hA : CarriesShift grading A q) (c : R) :
    CarriesShift grading (c • A) q := by
  intro m n hmn
  apply hA m n
  intro h
  apply hmn
  simp [h]

/-- Finite sums of maps with a common shift retain that shift. -/
theorem CarriesShift.sum (s : Finset ι)
    (A : ι → (Config →₀ R) →ₗ[R] (Config →₀ R))
    (q : G) (hA : ∀ i ∈ s, CarriesShift grading (A i) q) :
    CarriesShift grading (∑ i ∈ s, A i) q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (CarriesShift.zero grading q (R := R))
  | @insert i s hi ih =>
      have hhead : CarriesShift grading (A i) q :=
        hA i (Finset.mem_insert_self i s)
      have htail : ∀ j ∈ s, CarriesShift grading (A j) q := by
        intro j hj
        exact hA j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sum_insert hi] using hhead.add (ih htail)

/-- A map sending each basis vector to a multiple of a single basis vector
carries a shift when all nonzero multiples have the prescribed target grade. -/
theorem CarriesShift.of_single_smul {target : Config → Config} {coeff : Config → R}
    (hA : ∀ n, A (Finsupp.single n 1) = coeff n • Finsupp.single (target n) 1)
    (hshift : ∀ n, coeff n ≠ 0 → grading (target n) = grading n + q) :
    CarriesShift grading A q := by
  classical
  intro m n hmn
  rw [hA n] at hmn
  by_cases h : m = target n
  · subst m
    exact hshift n (by simpa using hmn)
  · exfalso
    apply hmn
    simp [Ne.symm h]

/-- Composition adds support shifts. -/
theorem CarriesShift.comp (hA : CarriesShift grading A qA) (hB : CarriesShift grading B qB) :
    CarriesShift grading (A.comp B) (qA + qB) := by
  intro m n hmn
  by_contra hshift
  apply hmn
  change A (B (Finsupp.single n 1)) m = 0
  rw [Finsupp.linearMap_apply_eq_finsetSum_of_support_subset A
    (B (Finsupp.single n 1)) (B (Finsupp.single n 1)).support (subset_refl _) m]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hAk : A (Finsupp.single k 1) m = 0
  · simp [hAk]
  · by_cases hBk : B (Finsupp.single n 1) k = 0
    · simp [hBk]
    · exfalso
      apply hshift
      calc
        grading m = grading k + qA := hA m k hAk
        _ = (grading n + qB) + qA := by rw [hB k n hBk]
        _ = grading n + (qA + qB) := by ac_rfl

/-- A nonzero shift forces every diagonal coordinate to vanish. -/
theorem CarriesShift.diagonal_eq_zero (hA : CarriesShift grading A q)
    (hq : q ≠ 0) (n : Config) : A (Finsupp.single n 1) n = 0 := by
  by_contra h
  have hshift := hA n n h
  have hEq : grading n + q = grading n + 0 := by simpa using hshift.symm
  exact hq (add_left_cancel hEq)

end Finsupp
