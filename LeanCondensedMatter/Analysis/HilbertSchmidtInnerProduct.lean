import LeanCondensedMatter.Analysis.HilbertSchmidtBasic

/-!
# The Hilbert–Schmidt inner product

Defines `innerHS d S T := Σᵢ ⟪S dᵢ, T dᵢ⟫` for `S`, `T` Hilbert–Schmidt with respect to a basis
`d`, and proves it's well-defined (summable) and basis-independent. See
`HilbertSchmidtBasic.lean`'s module docstring for the motivation, and
`HilbertSchmidtTrace.lean` for the reconciliation with `ContinuousLinearMap.trace`.
-/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Hilbert–Schmidt inner product, for a fixed basis.** `Σᵢ ⟪S dᵢ, T dᵢ⟫`; convergence
(for `S`, `T` Hilbert–Schmidt with respect to `d`) is `summable_inner_apply_of_isHilbertSchmidtWrt`
below, and independence of the choice of `d` is `innerHS_eq_of_isHilbertSchmidt`. -/
noncomputable def innerHS {ι : Type*} (d : HilbertBasis ι ℂ H) (S T : H →L[ℂ] H) : ℂ :=
  ∑' i, (inner ℂ (S (d i)) (T (d i)) : ℂ)

omit [CompleteSpace H] in
theorem summable_inner_apply_of_isHilbertSchmidtWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    {S T : H →L[ℂ] H} (hS : IsHilbertSchmidtWrt d S) (hT : IsHilbertSchmidtWrt d T) :
    Summable (fun i => (inner ℂ (S (d i)) (T (d i)) : ℂ)) := by
  refine Summable.of_norm_bounded ((hS.add hT).div_const 2) fun i => ?_
  have hab : ‖S (d i)‖ * ‖T (d i)‖ ≤ (‖S (d i)‖ ^ 2 + ‖T (d i)‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖S (d i)‖ - ‖T (d i)‖)]
  exact (norm_inner_le_norm (S (d i)) (T (d i))).trans hab

omit [CompleteSpace H] in
/-- **Absolute summability of the "resolution of the identity" double product**
`⟪S dᵢ, fⱼ⟫⟪fⱼ, T dᵢ⟫`, for `S`, `T` Hilbert–Schmidt with respect to `d` and *any* other basis
`f`. Established via the AM–GM bound `|ab| ≤ (|a|² + |b|²) / 2` (rather than
`summable_prod_of_nonneg` applied to the family itself, since the summands here are complex, not
nonnegative). The absolute-summability half of
`summable_inner_adjoint_apply_and_tsum_eq`'s argument, isolated since it doesn't need the
row/column identification that follows it. -/
theorem summable_inner_resolution_product {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H} (hSd : IsHilbertSchmidtWrt d S)
    (hTd : IsHilbertSchmidtWrt d T) :
    Summable (fun p : ι × κ =>
      (inner ℂ (S (d p.1)) (f p.2) : ℂ) * (inner ℂ (f p.2) (T (d p.1)) : ℂ)) := by
  classical
  set bd : ι × κ → ℝ :=
    fun p => (‖(inner ℂ (S (d p.1)) (f p.2) : ℂ)‖ ^ 2 +
      ‖(inner ℂ (f p.2) (T (d p.1)) : ℂ)‖ ^ 2) / 2 with hbd_def
  have hbd_nonneg : ∀ p, 0 ≤ bd p := fun p => by positivity
  have hg_le : ∀ p, ‖(inner ℂ (S (d p.1)) (f p.2) : ℂ) * (inner ℂ (f p.2) (T (d p.1)) : ℂ)‖ ≤
      bd p := fun p => by
    rw [hbd_def]
    simp only [norm_mul]
    nlinarith [sq_nonneg (‖(inner ℂ (S (d p.1)) (f p.2) : ℂ)‖ -
      ‖(inner ℂ (f p.2) (T (d p.1)) : ℂ)‖)]
  have hbd_row : ∀ i, HasSum (fun j => bd (i, j)) ((‖S (d i)‖ ^ 2 + ‖T (d i)‖ ^ 2) / 2) := by
    intro i
    have h1 : HasSum (fun j => ‖(inner ℂ (S (d i)) (f j) : ℂ)‖ ^ 2) (‖S (d i)‖ ^ 2) :=
      f.hasSum_norm_sq_inner (S (d i))
    have h2 : HasSum (fun j => ‖(inner ℂ (f j) (T (d i)) : ℂ)‖ ^ 2) (‖T (d i)‖ ^ 2) := by
      have heq : ∀ j, ‖(inner ℂ (f j) (T (d i)) : ℂ)‖ = ‖(inner ℂ (T (d i)) (f j) : ℂ)‖ :=
        fun j => by rw [← inner_conj_symm, RCLike.norm_conj]
      simp_rw [heq]
      exact f.hasSum_norm_sq_inner (T (d i))
    simpa only [hbd_def, add_div] using h1.div_const 2 |>.add (h2.div_const 2)
  have hbd_summable : Summable bd :=
    (summable_prod_of_nonneg hbd_nonneg).mpr ⟨fun i => (hbd_row i).summable, by
      simpa only [fun i => (hbd_row i).tsum_eq] using (hSd.add hTd).div_const 2⟩
  exact Summable.of_norm_bounded hbd_summable hg_le

/-- **The core Fubini computation underlying basis-independence of `innerHS`.** For `S`, `T`
Hilbert–Schmidt with respect to a basis `d`, and *any* other basis `f`, the double sum
`Σᵢⱼ ⟪S dᵢ, fⱼ⟫ ⟪fⱼ, T dᵢ⟫` (`summable_inner_resolution_product`) can be summed either row-first
(giving `Σᵢ ⟪S dᵢ, T dᵢ⟫`, via the resolution of the identity along `f`) or column-first (giving
`Σⱼ ⟪T† fⱼ, S† fⱼ⟫`, via the resolution of the identity along `d`, after rewriting each factor
with the adjoint). -/
theorem summable_inner_adjoint_apply_and_tsum_eq {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H} (hSd : IsHilbertSchmidtWrt d S)
    (hTd : IsHilbertSchmidtWrt d T) :
    Summable (fun j => (inner ℂ (ContinuousLinearMap.adjoint T (f j))
        (ContinuousLinearMap.adjoint S (f j)) : ℂ)) ∧
      ∑' j, (inner ℂ (ContinuousLinearMap.adjoint T (f j))
          (ContinuousLinearMap.adjoint S (f j)) : ℂ) =
        ∑' i, (inner ℂ (S (d i)) (T (d i)) : ℂ) := by
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
  obtain ⟨_, hcolSummable, heq⟩ := tsum_fiberwise_eq_of_summable hg_summable hrow hcol
  exact ⟨hcolSummable, heq.symm⟩

/-- **`innerHS` is independent of the choice of Hilbert basis.** Applying
`summable_inner_adjoint_apply_and_tsum_eq` with the same basis for both arguments identifies
`innerHS d S T` with `Σᵢ ⟪T† dᵢ, S† dᵢ⟫`; applying it again with `d` and `f` swapped identifies
the latter with `innerHS f S T`. -/
theorem innerHS_eq_of_isHilbertSchmidt {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : innerHS d S T = innerHS f S T := by
  have hSd := hS.isHilbertSchmidtWrt d
  have hTd := hT.isHilbertSchmidtWrt d
  have hSf := hS.isHilbertSchmidtWrt f
  have hTf := hT.isHilbertSchmidtWrt f
  have h2 := summable_inner_adjoint_apply_and_tsum_eq d d hSd hTd
  have h3 := summable_inner_adjoint_apply_and_tsum_eq f d hSf hTf
  exact h2.2.symm.trans h3.2

end ContinuousLinearMap
