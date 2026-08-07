import LeanCondensedMatter.Analysis.Operator.TraceClass.Diagonal
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Fredholm determinant for absolutely summable diagonal data

This module defines the first genuinely infinite-dimensional Fredholm determinant slice in the
project. For a scalar family `coeff : ι → ℂ` with `Summable (fun i => ‖coeff i‖)`, the determinant is

`∏' i, (1 + coeff i)`.

When `coeff` is used as the coefficient family of `HilbertBasis.diagonalOp`, this is the Fredholm
determinant of `1 + diagonalOp b coeff` in that explicit diagonal presentation. The definition is
not a determinant for arbitrary compact or trace-class operators, and it does not use the
finite-dimensional `ContinuousLinearMap.det` fallback.
-/

noncomputable section

namespace Fredholm

variable {ι κ : Type*}

/-- The Fredholm determinant attached to explicit diagonal coefficients `coeff`.

The definition is total, as is Mathlib's `tprod`; analytic theorems below state the absolute
summability hypothesis that guarantees convergence. -/
def diagonalDet (coeff : ι → ℂ) : ℂ :=
  ∏' i, (1 + coeff i)

/-- Absolute summability of diagonal coefficients guarantees convergence of the defining product. -/
theorem diagonalDet_multipliable (coeff : ι → ℂ)
    (hcoeff : Summable fun i => ‖coeff i‖) :
    Multipliable fun i => 1 + coeff i :=
  multipliable_one_add_of_summable hcoeff

/-- Equivalent enumerations of the same diagonal coefficients give the same determinant. -/
theorem diagonalDet_reindex (e : κ ≃ ι) (coeff : ι → ℂ) :
    diagonalDet (coeff ∘ e) = diagonalDet coeff := by
  simpa only [diagonalDet, Function.comp_apply] using
    e.tprod_eq (fun i => 1 + coeff i)

/-- The determinant of the zero diagonal perturbation is one. -/
@[simp]
theorem diagonalDet_zero : diagonalDet (fun _ : ι => 0) = 1 := by
  simp [diagonalDet]

/-- If the coefficient family vanishes outside a finite set, the Fredholm determinant reduces to
that finite product. -/
theorem diagonalDet_eq_finsetProd (coeff : ι → ℂ) (s : Finset ι)
    (hcoeff : ∀ i ∉ s, coeff i = 0) :
    diagonalDet coeff = ∏ i ∈ s, (1 + coeff i) := by
  unfold diagonalDet
  apply tprod_eq_prod
  intro i hi
  simp [hcoeff i hi]

/-- On a finite index type, the diagonal Fredholm determinant is the ordinary finite product of the
diagonal factors. -/
@[simp]
theorem diagonalDet_fintype [Fintype ι] (coeff : ι → ℂ) :
    diagonalDet coeff = ∏ i, (1 + coeff i) := by
  simp [diagonalDet]

/-- If no diagonal factor vanishes, the absolutely convergent determinant is nonzero. -/
theorem diagonalDet_ne_zero (coeff : ι → ℂ)
    (hcoeff : Summable fun i => ‖coeff i‖)
    (hfactor : ∀ i, 1 + coeff i ≠ 0) : diagonalDet coeff ≠ 0 :=
  tprod_one_add_ne_zero_of_summable hfactor hcoeff

/-- For absolutely summable diagonal data, the determinant vanishes exactly when one coefficient is
`-1`, equivalently when one factor `1 + coeff i` vanishes. -/
theorem diagonalDet_eq_zero_iff_exists_coeff_eq_neg_one (coeff : ι → ℂ)
    (hcoeff : Summable fun i => ‖coeff i‖) :
    diagonalDet coeff = 0 ↔ ∃ i, coeff i = -1 := by
  constructor
  · intro hdet
    by_contra hmissing
    apply (diagonalDet_ne_zero coeff hcoeff ?_) hdet
    intro i hzero
    apply hmissing
    have hzero' : coeff i + 1 = 0 := by
      simpa [add_comm] using hzero
    exact ⟨i, eq_neg_of_add_eq_zero_left hzero'⟩
  · rintro ⟨i, hi⟩
    unfold diagonalDet
    apply tprod_of_exists_eq_zero
    exact ⟨i, by simp [hi]⟩

end Fredholm

namespace HilbertBasis

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `1 + diagonalOp b coeff` acts diagonally with factors `1 + coeff i`. -/
theorem one_add_diagonalOp_apply_basis (b : HilbertBasis ι ℂ H) (coeff : ι → ℂ)
    (hcoeff : Summable fun i => ‖coeff i‖) (i : ι) :
    ((1 : H →L[ℂ] H) + diagonalOp b coeff) (b i) = (1 + coeff i) • b i := by
  change b i + diagonalOp b coeff (b i) = (1 + coeff i) • b i
  rw [diagonalOp_apply_basis b coeff hcoeff i]
  simp [add_smul]

/-- A coefficient `coeff i = -1` produces a nonzero kernel vector of
`1 + diagonalOp b coeff`. -/
theorem one_add_diagonalOp_has_nonzero_kernel_vector_of_coeff_eq_neg_one
    (b : HilbertBasis ι ℂ H) (coeff : ι → ℂ)
    (hcoeff : Summable fun i => ‖coeff i‖) (i : ι) (hi : coeff i = -1) :
    ∃ x : H, x ≠ 0 ∧ ((1 : H →L[ℂ] H) + diagonalOp b coeff) x = 0 := by
  refine ⟨b i, ?_, ?_⟩
  · intro hzero
    have hnorm := b.orthonormal.1 i
    simp [hzero] at hnorm
  · rw [one_add_diagonalOp_apply_basis b coeff hcoeff i, hi]
    simp

/-- Vanishing of the absolutely summable diagonal Fredholm determinant produces a nonzero kernel
vector of `1 + diagonalOp b coeff`. -/
theorem one_add_diagonalOp_has_nonzero_kernel_vector_of_diagonalDet_eq_zero
    (b : HilbertBasis ι ℂ H) (coeff : ι → ℂ)
    (hcoeff : Summable fun i => ‖coeff i‖) (hdet : Fredholm.diagonalDet coeff = 0) :
    ∃ x : H, x ≠ 0 ∧ ((1 : H →L[ℂ] H) + diagonalOp b coeff) x = 0 := by
  obtain ⟨i, hi⟩ :=
    (Fredholm.diagonalDet_eq_zero_iff_exists_coeff_eq_neg_one coeff hcoeff).mp hdet
  exact one_add_diagonalOp_has_nonzero_kernel_vector_of_coeff_eq_neg_one b coeff hcoeff i hi

end HilbertBasis
