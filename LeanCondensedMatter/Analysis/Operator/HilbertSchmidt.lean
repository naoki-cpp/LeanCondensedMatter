import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.MeanInequalities
import LeanCondensedMatter.Analysis.Operator.HilbertBasis
import Mathlib.Analysis.InnerProductSpace.Adjoint
import LeanCondensedMatter.Analysis.Operator.Compact
import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option linter.style.header false

/-!
# Hilbert–Schmidt operators: membership, pairing, norm, and compactness

This module defines Hilbert–Schmidt bounded operators on a Hilbert space and proves that
`Σᵢ ‖T dᵢ‖²`, when summable, has the same value for every Hilbert basis `d`. It also proves
closure of the Hilbert–Schmidt property under adjoints and composition with bounded operators.

The basis-independent square-summability condition supports the Hilbert–Schmidt inner product,
the canonical squared norm and its bounded-composition estimates, and the trace pairing
`Tr[S† ∘ T]` for Hilbert–Schmidt `S` and `T`, including non-self-adjoint products.
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
    simpa only [hg_def, norm_inner_symm (𝕜 := ℂ) (T (d i))] using
      f.hasSum_norm_sq_inner (T (d i))
  have hg_summable : Summable g :=
    (summable_prod_of_nonneg hg_nonneg).mpr ⟨fun i => (hrow i).summable, by
      simpa only [fun i => (hrow i).tsum_eq] using hd.summable⟩
  rw [← (hg_summable.hasSum.prod_fiberwise hrow).unique hd]
  exact hg_summable.hasSum

omit [CompleteSpace H] in
/-- The resolution-of-identity product is absolutely summable by Hölder's inequality
for the two square-summable matrix coefficient families. -/
private theorem summable_inner_resolution_product {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H} (hSd : IsHilbertSchmidtWrt d S)
    (hTd : IsHilbertSchmidtWrt d T) :
    Summable (fun p : ι × κ =>
      (inner ℂ (S (d p.1)) (f p.2) : ℂ) * (inner ℂ (f p.2) (T (d p.1)) : ℂ)) := by
  have h := Real.summable_mul_of_Lp_Lq_of_nonneg (p := 2) (q := 2)
    (f := fun p : ι × κ => ‖inner ℂ (S (d p.1)) (f p.2)‖)
    (g := fun p : ι × κ => ‖inner ℂ (T (d p.1)) (f p.2)‖)
    (by rw [Real.holderConjugate_iff]; norm_num)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (by simpa only [Real.rpow_two] using (hasSum_norm_sq_matrix_coeff d f S hSd.hasSum).summable)
    (by simpa only [Real.rpow_two] using (hasSum_norm_sq_matrix_coeff d f T hTd.hasSum).summable)
  refine Summable.of_norm_bounded h fun p => ?_
  change ‖(inner ℂ (S (d p.1)) (f p.2) : ℂ) * inner ℂ (f p.2) (T (d p.1))‖ ≤
    ‖inner ℂ (S (d p.1)) (f p.2)‖ * ‖inner ℂ (T (d p.1)) (f p.2)‖
  rw [norm_mul, norm_inner_symm (𝕜 := ℂ) (f p.2) (T (d p.1))]

/-- **The core Fubini computation underlying basis-independence of `innerHS`.** For `S`, `T`
Hilbert–Schmidt with respect to a basis `d`, and *any* other basis `f`, the double sum
`Σᵢⱼ ⟪S dᵢ, fⱼ⟫ ⟪fⱼ, T dᵢ⟫` (`summable_inner_resolution_product`) can be summed either row-first
(giving `Σᵢ ⟪S dᵢ, T dᵢ⟫`, via the resolution of the identity along `f`) or column-first (giving
`Σⱼ ⟪T† fⱼ, S† fⱼ⟫`, via the resolution of the identity along `d`, after rewriting each factor
with the adjoint). -/
private theorem hasSum_inner_adjoint_apply {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H} (hSd : IsHilbertSchmidtWrt d S)
    (hTd : IsHilbertSchmidtWrt d T) :
    HasSum (fun j => (inner ℂ (ContinuousLinearMap.adjoint T (f j))
        (ContinuousLinearMap.adjoint S (f j)) : ℂ))
      (∑' i, (inner ℂ (S (d i)) (T (d i)) : ℂ)) := by
  classical
  set g : ι × κ → ℂ :=
    fun p => (inner ℂ (S (d p.1)) (f p.2) : ℂ) * (inner ℂ (f p.2) (T (d p.1)) : ℂ) with hg_def
  have hg_summable : Summable g := summable_inner_resolution_product d f hSd hTd
  -- Row sums of `g`: the resolution of the identity along `f`, applied to `⟪S dᵢ, T dᵢ⟫`.
  have hrow : ∀ i, HasSum (fun j => g (i, j)) ((inner ℂ (S (d i)) (T (d i)) : ℂ)) := fun i =>
    f.hasSum_inner_mul_inner (S (d i)) (T (d i))
  -- Column sums of `g`: rewrite via the adjoint, then the resolution of the identity along `d`.
  have hcol : ∀ j, HasSum (fun i => g (i, j))
      ((inner ℂ (ContinuousLinearMap.adjoint T (f j)) (ContinuousLinearMap.adjoint S (f j)) :
        ℂ)) := fun j => by
    simpa only [hg_def, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right, mul_comm] using
      d.hasSum_inner_mul_inner (ContinuousLinearMap.adjoint T (f j))
        (ContinuousLinearMap.adjoint S (f j))
  have hcolSum := ((Equiv.prodComm κ ι).hasSum_iff.mpr hg_summable.hasSum).prod_fiberwise hcol
  rwa [← (hg_summable.hasSum.prod_fiberwise hrow).tsum_eq] at hcolSum

/-- The squared-norm adjoint identity is the diagonal specialization of the mixed
Hilbert–Schmidt pairing identity, transported from complex to real sums. -/
theorem hasSum_norm_sq_adjoint_apply {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) {a : ℝ}
    (hd : HasSum (fun i => ‖T (d i)‖ ^ 2) a) :
    HasSum (fun j => ‖(ContinuousLinearMap.adjoint T) (f j)‖ ^ 2) a := by
  have hself (x : H) : (inner ℂ x x : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    exact (inner_self_eq_norm_sq_to_K x).trans (Complex.ofReal_pow _ _).symm
  have hdiag : HasSum (fun i => (inner ℂ (T (d i)) (T (d i)) : ℂ)) (a : ℂ) := by
    simp_rw [hself]
    exact Complex.hasSum_ofReal.mpr hd
  have h := hasSum_inner_adjoint_apply d f (S := T) (T := T) hd.summable hd.summable
  rw [hdiag.tsum_eq] at h
  simp_rw [hself] at h
  exact Complex.hasSum_ofReal.mp h

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
/-- Pointwise squared-norm bound used by membership and norm estimates. -/
private theorem norm_sq_apply_le_opNorm_sq (B : H →L[ℂ] H) (x : H) :
    ‖B x‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖x‖ ^ 2 := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm x) 2

omit [CompleteSpace H] in
/-- Left composition by a bounded operator preserves Hilbert–Schmidt membership, using
the operator-norm bound on each vector in a witnessing Hilbert basis. -/
theorem isHilbertSchmidt_comp_left (B : H →L[ℂ] H) {T : H →L[ℂ] H}
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (B * T) := by
  obtain ⟨w, d, hd⟩ := hT
  refine ⟨w, d, ?_⟩
  exact Summable.of_nonneg_of_le (fun i => sq_nonneg _)
    (fun i => by simpa only [mul_apply_eq_comp] using norm_sq_apply_le_opNorm_sq B (T (d i)))
    (hd.mul_left (‖B‖ ^ 2))

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

/-! ## Hilbert–Schmidt inner product -/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Hilbert–Schmidt inner product, for a fixed basis.** `Σᵢ ⟪S dᵢ, T dᵢ⟫`.
Convergence for basis-independent Hilbert--Schmidt operators is exposed by
`IsHilbertSchmidt.summable_inner_apply`, and independence of the choice of `d` is
`innerHS_eq_of_isHilbertSchmidt`. -/
noncomputable def innerHS {ι : Type*} (d : HilbertBasis ι ℂ H) (S T : H →L[ℂ] H) : ℂ :=
  ∑' i, (inner ℂ (S (d i)) (T (d i)) : ℂ)

/-- **`innerHS` is independent of the choice of Hilbert basis.** Applying
`hasSum_inner_adjoint_apply` with the same basis for both arguments identifies
`innerHS d S T` with `Σᵢ ⟪T† dᵢ, S† dᵢ⟫`; applying it again with `d` and `f` swapped identifies
the latter with `innerHS f S T`. -/
theorem innerHS_eq_of_isHilbertSchmidt {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : innerHS d S T = innerHS f S T := by
  exact (hasSum_inner_adjoint_apply d d
    (hS.summable_norm_sq_apply d) (hT.summable_norm_sq_apply d)).tsum_eq.symm.trans
    (hasSum_inner_adjoint_apply f d
      (hS.summable_norm_sq_apply f) (hT.summable_norm_sq_apply f)).tsum_eq

/-- Right composition can be transferred between the two Hilbert--Schmidt factors by taking the
adjoint:
`⟪S, T W⟫_{HS} = ⟪S W†, T⟫_{HS}`. -/
theorem innerHS_comp_right {ι : Type*} (d : HilbertBasis ι ℂ H)
    {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T)
    (W : H →L[ℂ] H) :
    innerHS d S (T * W) =
      innerHS d (S * ContinuousLinearMap.adjoint W) T := by
  have hleft := hasSum_inner_adjoint_apply d d
    (hS.summable_norm_sq_apply d)
    ((isHilbertSchmidt_comp_right hT W).summable_norm_sq_apply d)
  have hright := hasSum_inner_adjoint_apply d d
    ((isHilbertSchmidt_comp_right hS (ContinuousLinearMap.adjoint W)).summable_norm_sq_apply d)
    (hT.summable_norm_sq_apply d)
  unfold innerHS
  calc
    (∑' i, (inner ℂ (S (d i)) ((T * W) (d i)) : ℂ)) =
        ∑' i, (inner ℂ (ContinuousLinearMap.adjoint (T * W) (d i))
          (ContinuousLinearMap.adjoint S (d i)) : ℂ) := hleft.tsum_eq.symm
    _ = ∑' i, (inner ℂ (ContinuousLinearMap.adjoint T (d i))
          (ContinuousLinearMap.adjoint (S * ContinuousLinearMap.adjoint W) (d i)) : ℂ) := by
      apply tsum_congr
      intro i
      simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply] using
        (ContinuousLinearMap.adjoint_inner_left W
          (ContinuousLinearMap.adjoint S (d i)) (ContinuousLinearMap.adjoint T (d i)))
    _ = ∑' i, (inner ℂ ((S * ContinuousLinearMap.adjoint W) (d i)) (T (d i)) : ℂ) :=
      hright.tsum_eq

end ContinuousLinearMap

/-! ## Squared Hilbert–Schmidt norm -/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsHilbertSchmidt

/-- The basis-independent squared Hilbert--Schmidt norm. -/
noncomputable def normSq {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) : ℝ :=
  let w : Set H := Classical.choose hT
  let hw : ∃ d : HilbertBasis w ℂ H, IsHilbertSchmidtWrt d T :=
    Classical.choose_spec hT
  let d : HilbertBasis w ℂ H := Classical.choose hw
  ∑' i, ‖T (d i)‖ ^ 2

/-- The square-norm family in every Hilbert basis sums to the canonical Hilbert--Schmidt norm
square. -/
theorem hasSum_norm_sq_apply {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => ‖T (d i)‖ ^ 2) hT.normSq := by
  unfold normSq
  exact hasSum_norm_sq_apply_of_hasSum _ d T (hT.summable_norm_sq_apply _).hasSum

/-- The squared Hilbert--Schmidt norm is the square-norm sum in every Hilbert basis. -/
theorem normSq_eq_tsum_norm_sq_apply {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.normSq = ∑' i, ‖T (d i)‖ ^ 2 :=
  (hT.hasSum_norm_sq_apply d).tsum_eq.symm

omit [CompleteSpace H] in
/-- The squared Hilbert--Schmidt norm is nonnegative. -/
theorem normSq_nonneg {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    0 ≤ hT.normSq := by
  unfold normSq
  exact tsum_nonneg fun _ => sq_nonneg _

/-- The squared Hilbert--Schmidt norm is strictly positive for a nonzero operator. -/
theorem normSq_pos {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (hne : T ≠ 0) :
    0 < hT.normSq := by
  by_contra! hle
  obtain ⟨w, b, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hb (i : w) : T (b i) = 0 := by
    by_contra hi
    apply (not_lt_of_ge hle)
    rw [hT.normSq_eq_tsum_norm_sq_apply b]
    exact (hT.summable_norm_sq_apply b).tsum_pos (fun _ => sq_nonneg _) i
      (pow_pos (norm_pos_iff.mpr hi) 2)
  apply hne
  ext x
  have hsum := (b.hasSum_repr x).mapL T
  simpa [hb] using hsum.tsum_eq.symm

/-- Taking the adjoint preserves the squared Hilbert--Schmidt norm. -/
theorem normSq_adjoint {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    (isHilbertSchmidt_adjoint hT).normSq = hT.normSq := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  exact ((isHilbertSchmidt_adjoint hT).hasSum_norm_sq_apply d).unique
    (hasSum_norm_sq_adjoint_apply d d T (hT.hasSum_norm_sq_apply d))

/-- Left composition by a bounded operator increases the squared Hilbert--Schmidt norm by at most
the square of the operator norm. -/
theorem normSq_comp_left_le (hT : IsHilbertSchmidt T) (B : H →L[ℂ] H) :
    (isHilbertSchmidt_comp_left B hT).normSq ≤ ‖B‖ ^ 2 * hT.normSq := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  exact hasSum_le
    (fun i => by simpa only [mul_apply_eq_comp] using norm_sq_apply_le_opNorm_sq B (T (d i)))
    ((isHilbertSchmidt_comp_left B hT).hasSum_norm_sq_apply d)
    ((hT.hasSum_norm_sq_apply d).mul_left (‖B‖ ^ 2))

/-- Right composition by a bounded operator increases the squared Hilbert--Schmidt norm by at most
the square of the operator norm. -/
theorem normSq_comp_right_le (hT : IsHilbertSchmidt T) (B : H →L[ℂ] H) :
    (isHilbertSchmidt_comp_right hT B).normSq ≤ ‖B‖ ^ 2 * hT.normSq := by
  have hnorm :
      (isHilbertSchmidt_comp_left (ContinuousLinearMap.adjoint B)
        (isHilbertSchmidt_adjoint hT)).normSq =
        (isHilbertSchmidt_comp_right hT B).normSq := by
    simpa only [← ContinuousLinearMap.star_eq_adjoint, star_mul] using
      (isHilbertSchmidt_comp_right hT B).normSq_adjoint
  have h := (isHilbertSchmidt_adjoint hT).normSq_comp_left_le
    (ContinuousLinearMap.adjoint B)
  rw [hnorm, hT.normSq_adjoint, ← ContinuousLinearMap.star_eq_adjoint, norm_star] at h
  exact h

/-- Right composition by a contraction does not increase the squared Hilbert--Schmidt norm. -/
theorem normSq_comp_right_le_of_norm_le_one (hT : IsHilbertSchmidt T)
    (B : H →L[ℂ] H) (hB : ‖B‖ ≤ 1) :
    (isHilbertSchmidt_comp_right hT B).normSq ≤ hT.normSq := by
  refine (hT.normSq_comp_right_le B).trans ?_
  simpa only [one_pow, one_mul] using
    mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg B) hB 2) hT.normSq_nonneg

/-- The absolute diagonal pairing is summable and bounded by the product of the
Hilbert--Schmidt norms, by Hölder's inequality for the square-summable norm families. -/
theorem summable_norm_inner_apply_and_tsum_le {S T : H →L[ℂ] H}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖inner ℂ (S (d i)) (T (d i))‖) ∧
      ∑' i, ‖inner ℂ (S (d i)) (T (d i))‖ ≤
        Real.sqrt hS.normSq * Real.sqrt hT.normSq := by
  obtain ⟨hsum, hC⟩ :=
    Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg (p := 2) (q := 2)
      (f := fun i => ‖S (d i)‖) (g := fun i => ‖T (d i)‖)
      (by rw [Real.holderConjugate_iff]; norm_num)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (by simpa only [Real.rpow_two] using hS.summable_norm_sq_apply d)
      (by simpa only [Real.rpow_two] using hT.summable_norm_sq_apply d)
  have hle (i : ι) : ‖inner ℂ (S (d i)) (T (d i))‖ ≤
      ‖S (d i)‖ * ‖T (d i)‖ :=
    norm_inner_le_norm (S (d i)) (T (d i))
  have hinner : Summable (fun i => ‖inner ℂ (S (d i)) (T (d i))‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hle hsum
  refine ⟨hinner, (hinner.tsum_le_tsum hle hsum).trans ?_⟩
  simpa only [Real.rpow_two, (hS.hasSum_norm_sq_apply d).tsum_eq,
    (hT.hasSum_norm_sq_apply d).tsum_eq, ← Real.sqrt_eq_rpow] using hC

/-- The Hilbert--Schmidt diagonal pairing is summable in every Hilbert basis. -/
theorem summable_inner_apply {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    Summable (fun i => (inner ℂ (S (d i)) (T (d i)) : ℂ)) :=
  Summable.of_norm (hS.summable_norm_inner_apply_and_tsum_le hT d).1

end IsHilbertSchmidt

end ContinuousLinearMap

/-!
## Compactness of Hilbert--Schmidt operators

Hilbert--Schmidt operators are compact. The proof approximates an operator in operator norm by
finite sums of rank-one operators obtained from a Hilbert basis.
-/

noncomputable section

open Filter Topology

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsHilbertSchmidt

private noncomputable def finiteRangeApprox {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (s : Finset ι) : H →L[ℂ] H :=
  ∑ i ∈ s, InnerProductSpace.rankOne ℂ (d i) ((ContinuousLinearMap.adjoint T) (d i))

private theorem finiteRangeApprox_isCompact {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (s : Finset ι) :
    IsCompactOperator (finiteRangeApprox d T s) := by
  change finiteRangeApprox d T s ∈ compactOperator (RingHom.id ℂ) H H
  exact Submodule.sum_mem _ fun i _ =>
    InnerProductSpace.isCompactOperator_rankOne (d i) ((ContinuousLinearMap.adjoint T) (d i))

private theorem inner_finiteRangeApprox_apply {ι : Type*} [DecidableEq ι]
    (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (s : Finset ι) (x : H) (j : ι) :
    inner ℂ (d j) ((finiteRangeApprox d T s) x) =
      if j ∈ s then inner ℂ (d j) (T x) else 0 := by
  simp [finiteRangeApprox, InnerProductSpace.rankOne_apply, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp d.orthonormal, ContinuousLinearMap.adjoint_inner_left]

private theorem norm_sub_finiteRangeApprox_le {ι : Type*} (d : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] H} (hd : Summable (fun i => ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2))
    (s : Finset ι) :
    ‖T - finiteRangeApprox d T s‖ ≤
      Real.sqrt (∑' i : {j // j ∉ s}, ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2) := by
  classical
  let tail : ℝ := ∑' i : {j // j ∉ s}, ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2
  have htail_nonneg : 0 ≤ tail := tsum_nonneg fun _ => sq_nonneg _
  refine (T - finiteRangeApprox d T s).opNorm_le_bound (Real.sqrt_nonneg tail) fun x => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg tail) (norm_nonneg x)),
    mul_pow, Real.sq_sqrt htail_nonneg]
  have hzero :
      ∑ i ∈ s, ‖(inner ℂ (d i) ((T - finiteRangeApprox d T s) x) : ℂ)‖ ^ 2 = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp [sub_apply, inner_sub_right, inner_finiteRangeApprox_apply, hi]
  have htail := s.hasSum_iff_compl.mp
    (d.hasSum_norm_sq_inner ((T - finiteRangeApprox d T s) x))
  rw [hzero, sub_zero] at htail
  exact hasSum_le (fun i => by
    rw [sub_apply, inner_sub_right, inner_finiteRangeApprox_apply, ite_eq_right i.2, sub_zero,
      ← ContinuousLinearMap.adjoint_inner_left T x (d i), Function.comp_apply, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_inner_le_norm ((ContinuousLinearMap.adjoint T) (d i)) x) 2)
    htail ((hd.subtype {j | j ∉ s}).hasSum.mul_right (‖x‖ ^ 2))

/-- Every Hilbert--Schmidt operator is compact. -/
theorem isCompact {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    IsCompactOperator T := by
  classical
  obtain ⟨ι, d, hd⟩ := isHilbertSchmidt_adjoint hT
  let tail : Finset ι → ℝ := fun s =>
    ∑' i : {j // j ∉ s}, ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2
  have htail : Tendsto tail atTop (𝓝 0) := by
    simpa [tail] using
      (tendsto_tsum_compl_atTop_zero
        (fun i : ι => ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2))
  have happ : Tendsto (finiteRangeApprox d T) atTop (𝓝 T) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    refine squeeze_zero (fun s => norm_nonneg _)
      (fun s => ?_) (by simpa using htail.sqrt)
    simpa [norm_sub_rev, tail] using norm_sub_finiteRangeApprox_le d hd s
  exact isCompactOperator_of_tendsto happ
    (Filter.Eventually.of_forall (finiteRangeApprox_isCompact d T))

end IsHilbertSchmidt

end ContinuousLinearMap
