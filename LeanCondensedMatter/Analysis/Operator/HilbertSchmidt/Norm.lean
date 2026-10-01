import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Basic

set_option linter.style.header false

/-!
# Hilbert--Schmidt norm-square series

This module owns the basis-relative totalized series
`Σᵢ ‖T dᵢ‖²`. For Hilbert--Schmidt operators its value is independent of the Hilbert basis.
The unrestricted definition is a totalized `tsum`; outside Hilbert--Schmidt membership it is not
assigned Hilbert--Schmidt norm meaning.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The totalized square-norm series of `T` in a Hilbert basis. -/
noncomputable def hilbertSchmidtNormSqSeriesWrt {ι : Type*}
    (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : ℝ :=
  ∑' i, ‖T (d i)‖ ^ 2

/-- For a Hilbert--Schmidt operator, the square-norm series has the same value in every Hilbert
basis. -/
theorem hilbertSchmidtNormSqSeriesWrt_eq {ι κ : Type*}
    (d : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ H)
    (T : H →L[ℂ] H) (hT : IsHilbertSchmidt T) :
    hilbertSchmidtNormSqSeriesWrt d T = hilbertSchmidtNormSqSeriesWrt f T := by
  unfold hilbertSchmidtNormSqSeriesWrt
  exact (summable_norm_sq_apply_and_tsum_eq d f T (hT.isHilbertSchmidtWrt d)).2.symm

end ContinuousLinearMap
