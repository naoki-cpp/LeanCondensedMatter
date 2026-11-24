import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Hilbert–Schmidt operators: predicate and basis independence

This module defines Hilbert–Schmidt bounded operators on a Hilbert space and proves that
`Σᵢ ‖T dᵢ‖²`, when summable, has the same value for every Hilbert basis `d`. It also proves
closure of the Hilbert–Schmidt property under adjoints and composition with bounded operators.

The basis-independent square-summability condition supports the Hilbert–Schmidt inner product and
the trace pairing `Tr[S† ∘ T]` for Hilbert–Schmidt `S` and `T`, including cases where
`S† ∘ T` is not self-adjoint.
-/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `T` is Hilbert–Schmidt with respect to a given Hilbert basis `d`: the squared norms of its
images on the basis vectors are summable. Its relation to the basis-independent predicate is
`isHilbertSchmidt_iff_isHilbertSchmidtWrt`. -/
def IsHilbertSchmidtWrt {ι : Type*} (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : Prop :=
  Summable (fun i => ‖T (d i)‖ ^ 2)

omit [CompleteSpace H] in
/-- The squared matrix coefficients over any two Hilbert bases sum to the
square-norm sum of the operator images on the domain basis. -/
theorem hasSum_norm_sq_matrix_coeff {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) {a : ℝ}
    (hd : HasSum (fun i => ‖T (d i)‖ ^ 2) a) :
    HasSum (fun p : ι × κ => ‖(inner ℂ (T (d p.1)) (f p.2) : ℂ)‖ ^ 2) a := by
  classical
  set g : ι × κ → ℝ := fun p => ‖(inner ℂ (T (d p.1)) (f p.2) : ℂ)‖ ^ 2 with hg_def
  have hg_nonneg : ∀ p, 0 ≤ g p := fun p => sq_nonneg _
  have hrow : ∀ i, HasSum (fun j => g (i, j)) (‖T (d i)‖ ^ 2) := fun i => by
    simpa only [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two,
      f.repr_apply_apply, f.repr.norm_map, norm_inner_symm, hg_def] using
      (lp.hasSum_norm (p := 2) (by norm_num) (f.repr (T (d i))))
  have hg_summable : Summable g :=
    (summable_prod_of_nonneg hg_nonneg).mpr ⟨fun i => (hrow i).summable, by
      simpa only [fun i => (hrow i).tsum_eq] using hd.summable⟩
  rw [← (hg_summable.hasSum.prod_fiberwise hrow).unique hd]
  exact hg_summable.hasSum

/-- **The core basis-independence computation.** If `T` is Hilbert–Schmidt with respect to a
basis `d`, then its adjoint `T†` is Hilbert–Schmidt with respect to *any* basis `f`, with the same
sum of squared norms. -/
theorem hasSum_norm_sq_adjoint_apply {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) {a : ℝ}
    (hd : HasSum (fun i => ‖T (d i)‖ ^ 2) a) :
    HasSum (fun j => ‖(ContinuousLinearMap.adjoint T) (f j)‖ ^ 2) a := by
  classical
  set g : ι × κ → ℝ := fun p => ‖(inner ℂ (T (d p.1)) (f p.2) : ℂ)‖ ^ 2 with hg_def
  have hg : HasSum g a := hasSum_norm_sq_matrix_coeff d f T hd
  have hcol : ∀ j, HasSum (fun i => g (i, j)) (‖(ContinuousLinearMap.adjoint T) (f j)‖ ^ 2) :=
    fun j => by
      simpa only [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two,
        d.repr_apply_apply, d.repr.norm_map, hg_def, ContinuousLinearMap.adjoint_inner_right] using
        (lp.hasSum_norm (p := 2) (by norm_num) (d.repr ((ContinuousLinearMap.adjoint T) (f j))))
  exact ((Equiv.prodComm κ ι).hasSum_iff.mpr hg).prod_fiberwise hcol

/-- **The same basis-independence, phrased for `T` itself rather than its adjoint.** Applying
`hasSum_norm_sq_adjoint_apply` twice — once for `T`, once for `T†` — and using
`T†† = T` transports the sum of squared norms of `T` from any one basis to any other. This
value-level result underlies the canonical basis-independent characterization below. -/
theorem hasSum_norm_sq_apply_of_hasSum {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) {a : ℝ}
    (hd : HasSum (fun i => ‖T (d i)‖ ^ 2) a) :
    HasSum (fun j => ‖T (f j)‖ ^ 2) a := by
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    hasSum_norm_sq_adjoint_apply f f (ContinuousLinearMap.adjoint T)
      (hasSum_norm_sq_adjoint_apply d f T hd)

/-- **`T` is Hilbert–Schmidt**, independently of any particular choice of Hilbert basis. -/
def IsHilbertSchmidt (T : H →L[ℂ] H) : Prop :=
  ∃ (w : Set H) (d : HilbertBasis w ℂ H), IsHilbertSchmidtWrt d T

theorem isHilbertSchmidt_iff_isHilbertSchmidtWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) : IsHilbertSchmidt T ↔ IsHilbertSchmidtWrt d T := by
  constructor
  · rintro ⟨ι', d', hd'⟩
    exact (hasSum_norm_sq_apply_of_hasSum d' d T hd'.hasSum).summable
  · intro hd
    obtain ⟨w, e, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
    exact ⟨w, e, (hasSum_norm_sq_apply_of_hasSum d e T hd.hasSum).summable⟩

namespace IsHilbertSchmidt

/-- A Hilbert--Schmidt operator has square-summable images in every Hilbert basis. -/
theorem summable_norm_sq_apply {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖T (d i)‖ ^ 2) :=
  (isHilbertSchmidt_iff_isHilbertSchmidtWrt d T).mp hT

end IsHilbertSchmidt

/-- **Hilbert–Schmidt-ness is preserved by taking the adjoint.** A direct consequence of the
basis-independence computation: `T` being Hilbert–Schmidt with respect to `d` already gives that
`T†` is Hilbert–Schmidt with respect to that *same* `d` (no basis change needed for this
direction). -/
theorem isHilbertSchmidt_adjoint {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (ContinuousLinearMap.adjoint T) := by
  obtain ⟨w, d, hd⟩ := hT
  exact ⟨w, d, (hasSum_norm_sq_adjoint_apply d d T hd.hasSum).summable⟩

omit [CompleteSpace H] in
/-- Left composition by a bounded operator preserves Hilbert–Schmidt membership, using
the operator-norm bound on each vector in a witnessing Hilbert basis. -/
theorem isHilbertSchmidt_comp_left (B : H →L[ℂ] H) {T : H →L[ℂ] H}
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (B * T) := by
  obtain ⟨w, d, hd⟩ := hT
  refine ⟨w, d, ?_⟩
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_)
    (hd.mul_left (‖B‖ ^ 2))
  rw [mul_apply_eq_comp, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm (T (d i))) 2

/-- **Composing a Hilbert–Schmidt operator with a bounded operator on the right stays
Hilbert–Schmidt.** Reduced to the left-composition case via the adjoint identity
`(T * B)† = B† * T†`: `T†` is Hilbert–Schmidt (`isHilbertSchmidt_adjoint`), so `B† * T†` is
Hilbert–Schmidt (`isHilbertSchmidt_comp_left`), so its adjoint `T * B` is Hilbert–Schmidt
(`isHilbertSchmidt_adjoint` again, using `T†† = T`). -/
theorem isHilbertSchmidt_comp_right {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    (B : H →L[ℂ] H) : IsHilbertSchmidt (T * B) := by
  simpa only [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star] using
    (isHilbertSchmidt_adjoint
      (isHilbertSchmidt_comp_left (ContinuousLinearMap.adjoint B)
        (isHilbertSchmidt_adjoint hT)))

end ContinuousLinearMap
