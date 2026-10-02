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

namespace IsHilbertSchmidt

/-- The basis-independent squared Hilbert--Schmidt norm. -/
noncomputable def normSq {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) : ℝ :=
  let w : Set H := Classical.choose hT
  let hw : ∃ d : HilbertBasis w ℂ H, IsHilbertSchmidtWrt d T :=
    Classical.choose_spec hT
  let d : HilbertBasis w ℂ H := Classical.choose hw
  hilbertSchmidtNormSqSeriesWrt d T

/-- The squared Hilbert--Schmidt norm is the square-norm series in every Hilbert basis. -/
theorem normSq_eq_seriesWrt {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.normSq = hilbertSchmidtNormSqSeriesWrt d T := by
  unfold normSq
  exact hilbertSchmidtNormSqSeriesWrt_eq _ d T hT

/-- The squared Hilbert--Schmidt norm is independent of the proof of membership. -/
theorem normSq_proof_irrel {T : H →L[ℂ] H} (hT hT' : IsHilbertSchmidt T) :
    hT.normSq = hT'.normSq := by
  exact congrArg normSq (Subsingleton.elim hT hT')

/-- The squared Hilbert--Schmidt norm is nonnegative. -/
theorem normSq_nonneg {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    0 ≤ hT.normSq := by
  unfold normSq hilbertSchmidtNormSqSeriesWrt
  exact tsum_nonneg fun _ => sq_nonneg _

end IsHilbertSchmidt

end ContinuousLinearMap
