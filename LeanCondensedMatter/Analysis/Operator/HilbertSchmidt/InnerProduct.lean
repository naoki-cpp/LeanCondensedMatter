import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Basic

/-!
# The Hilbert–Schmidt inner product

Defines `innerHS d S T := Σᵢ ⟪S dᵢ, T dᵢ⟫` for `S`, `T` Hilbert–Schmidt with respect to a basis
`d`, and proves it is well-defined and basis-independent through the basis-independent
`IsHilbertSchmidt` predicate. See the `Basic` module for the underlying Hilbert–Schmidt
membership API.
-/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Hilbert–Schmidt inner product, for a fixed basis.** `Σᵢ ⟪S dᵢ, T dᵢ⟫`.
Convergence for basis-independent Hilbert--Schmidt operators is exposed by
`IsHilbertSchmidt.summable_inner_apply`, and independence of the choice of `d` is
`innerHS_eq_of_isHilbertSchmidt`. -/
noncomputable def innerHS {ι : Type*} (d : HilbertBasis ι ℂ H) (S T : H →L[ℂ] H) : ℂ :=
  ∑' i, (inner ℂ (S (d i)) (T (d i)) : ℂ)

namespace IsHilbertSchmidt

/-- The Hilbert--Schmidt diagonal pairing is summable in every Hilbert basis. -/
theorem summable_inner_apply {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    Summable (fun i => (inner ℂ (S (d i)) (T (d i)) : ℂ)) := by
  refine Summable.of_norm_bounded
    (((hS.summable_norm_sq_apply d).add (hT.summable_norm_sq_apply d)).div_const 2)
    fun i => ?_
  exact (norm_inner_le_norm (S (d i)) (T (d i))).trans (by
    nlinarith [sq_nonneg (‖S (d i)‖ - ‖T (d i)‖)])

/-- The Hilbert--Schmidt diagonal pairing sums to `innerHS` in every Hilbert basis. -/
theorem hasSum_innerHS {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => (inner ℂ (S (d i)) (T (d i)) : ℂ)) (innerHS d S T) := by
  unfold innerHS
  exact (hS.summable_inner_apply hT d).hasSum

end IsHilbertSchmidt

omit [CompleteSpace H] in
/-- The resolution-of-identity product is absolutely summable by Hölder's inequality
for the two square-summable matrix coefficient families. -/
private theorem summable_inner_resolution_product {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H} (hSd : IsHilbertSchmidtWrt d S)
    (hTd : IsHilbertSchmidtWrt d T) :
    Summable (fun p : ι × κ =>
      (inner ℂ (S (d p.1)) (f p.2) : ℂ) * (inner ℂ (f p.2) (T (d p.1)) : ℂ)) := by
  let coeff (A : H →L[ℂ] H) (hA : IsHilbertSchmidtWrt d A) : lp (fun _ : ι × κ => ℂ) 2 :=
    ⟨fun p => inner ℂ (A (d p.1)) (f p.2), by
      change Memℓp (fun p : ι × κ => inner ℂ (A (d p.1)) (f p.2)) 2
      refine (memℓp_gen_iff (p := 2) (by norm_num)).2 ?_
      simpa only [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two] using
        (hasSum_norm_sq_matrix_coeff d f A hA.hasSum).summable⟩
  have h := lp.summable_mul (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num) (coeff S hSd) (coeff T hTd)
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
  have hcol_point : ∀ i j, g (i, j) =
      (inner ℂ (ContinuousLinearMap.adjoint T (f j)) (d i) : ℂ) *
        (inner ℂ (d i) (ContinuousLinearMap.adjoint S (f j)) : ℂ) := fun i j => by
    rw [hg_def]
    simp only
    rw [← ContinuousLinearMap.adjoint_inner_right S (d i) (f j),
      ← ContinuousLinearMap.adjoint_inner_left T (d i) (f j), mul_comm]
  have hcol : ∀ j, HasSum (fun i => g (i, j))
      ((inner ℂ (ContinuousLinearMap.adjoint T (f j)) (ContinuousLinearMap.adjoint S (f j)) :
        ℂ)) := fun j => by
    simp_rw [hcol_point]
    exact d.hasSum_inner_mul_inner (ContinuousLinearMap.adjoint T (f j))
      (ContinuousLinearMap.adjoint S (f j))
  have hcolSum := ((Equiv.prodComm κ ι).hasSum_iff.mpr hg_summable.hasSum).prod_fiberwise hcol
  rwa [← (hg_summable.hasSum.prod_fiberwise hrow).tsum_eq] at hcolSum

/-- **`innerHS` is independent of the choice of Hilbert basis.** Applying
`hasSum_inner_adjoint_apply` with the same basis for both arguments identifies
`innerHS d S T` with `Σᵢ ⟪T† dᵢ, S† dᵢ⟫`; applying it again with `d` and `f` swapped identifies
the latter with `innerHS f S T`. -/
theorem innerHS_eq_of_isHilbertSchmidt {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : innerHS d S T = innerHS f S T := by
  have hSd := hS.summable_norm_sq_apply d
  have hTd := hT.summable_norm_sq_apply d
  have hSf := hS.summable_norm_sq_apply f
  have hTf := hT.summable_norm_sq_apply f
  have h2 := hasSum_inner_adjoint_apply d d hSd hTd
  have h3 := hasSum_inner_adjoint_apply f d hSf hTf
  exact h2.tsum_eq.symm.trans h3.tsum_eq

/-- Right composition can be transferred between the two Hilbert--Schmidt factors by taking the
adjoint:
`⟪S, T W⟫_{HS} = ⟪S W†, T⟫_{HS}`. -/
theorem innerHS_comp_right {ι : Type*} (d : HilbertBasis ι ℂ H)
    {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T)
    (W : H →L[ℂ] H) :
    innerHS d S (T * W) =
      innerHS d (S * ContinuousLinearMap.adjoint W) T := by
  have hTW : IsHilbertSchmidt (T * W) := isHilbertSchmidt_comp_right hT W
  have hSW : IsHilbertSchmidt (S * ContinuousLinearMap.adjoint W) :=
    isHilbertSchmidt_comp_right hS (ContinuousLinearMap.adjoint W)
  have hleft := hasSum_inner_adjoint_apply d d
    (hS.summable_norm_sq_apply d)
    (hTW.summable_norm_sq_apply d)
  have hright := hasSum_inner_adjoint_apply d d
    (hSW.summable_norm_sq_apply d)
    (hT.summable_norm_sq_apply d)
  have hAdjTW :
      ContinuousLinearMap.adjoint (T * W) =
        ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint T := by
    simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul]
  have hAdjSW :
      ContinuousLinearMap.adjoint (S * ContinuousLinearMap.adjoint W) =
        W * ContinuousLinearMap.adjoint S := by
    simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star]
  unfold innerHS
  calc
    (∑' i, (inner ℂ (S (d i)) ((T * W) (d i)) : ℂ)) =
        ∑' i, (inner ℂ (ContinuousLinearMap.adjoint (T * W) (d i))
          (ContinuousLinearMap.adjoint S (d i)) : ℂ) := hleft.tsum_eq.symm
    _ = ∑' i, (inner ℂ (ContinuousLinearMap.adjoint T (d i))
          (ContinuousLinearMap.adjoint (S * ContinuousLinearMap.adjoint W) (d i)) : ℂ) := by
      apply tsum_congr
      intro i
      rw [hAdjTW, hAdjSW, mul_apply_eq_comp, mul_apply_eq_comp]
      exact ContinuousLinearMap.adjoint_inner_left W
        (ContinuousLinearMap.adjoint S (d i))
        (ContinuousLinearMap.adjoint T (d i))
    _ = ∑' i, (inner ℂ ((S * ContinuousLinearMap.adjoint W) (d i)) (T (d i)) : ℂ) :=
      hright.tsum_eq

end ContinuousLinearMap
