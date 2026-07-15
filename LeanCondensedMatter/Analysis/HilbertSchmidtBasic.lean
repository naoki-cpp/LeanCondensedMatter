import LeanCondensedMatter.Analysis.TraceClassOps
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Hilbert–Schmidt operators: the predicate and its basis-independence

Defines the Hilbert–Schmidt class of (possibly non-self-adjoint) bounded operators on a Hilbert
space, and proves the fundamental basis-independence fact that makes it well-defined:
`Σᵢ ‖T dᵢ‖²` has the same value (finite or not) for every Hilbert basis `d`. Also proves
Hilbert–Schmidt-ness is preserved under taking the adjoint and under composition with a bounded
operator.

**Motivation.** `ContinuousLinearMap.trace` (`Analysis/TraceClassBasic.lean`) is only defined
for compact self-adjoint trace-class operators. The Born-rule probability `Tr[E_m ρ]` needs a
trace for `E_m ∘ ρ`, which need not be self-adjoint even when `E_m` and `ρ` both are (a product
of self-adjoint operators is self-adjoint only when they commute). The standard fix: if `S`, `T`
are both Hilbert–Schmidt, `S† ∘ T` is trace-class regardless of self-adjointness, with
`Tr[S† ∘ T] = Σᵢ ⟪S dᵢ, T dᵢ⟫` well-defined via the Hilbert–Schmidt inner product
(`HilbertSchmidtInnerProduct.lean`). This file lays the groundwork: the Hilbert–Schmidt predicate
and its basis-independence. See `notes/roadmaps/operator-algebra.md`.
-/

/-- **Row-first and column-first iterated sums of a summable double family agree, with each
individually summable.** Given `g : ι × κ → E` summable, together with `HasSum` data for its row
sums (`row i = Σⱼ g(i,j)`) and column sums (`col j = Σᵢ g(i,j)`), `row` and `col` are themselves
summable with a common total `Σᵢ row i = Σⱼ col j = Σ g`. The Fubini-style swap
(`Summable.prod_symm`/`Equiv.prodComm`/`HasSum.prod_fiberwise`) underlying both
`summable_norm_sq_adjoint_apply_and_tsum_eq` and `summable_inner_adjoint_apply_and_tsum_eq`
(`HilbertSchmidtInnerProduct.lean`), factored out since neither proof depends on `E` being `ℝ` or
`ℂ` specifically. -/
theorem tsum_fiberwise_eq_of_summable {ι κ E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {g : ι × κ → E} {row : ι → E} {col : κ → E} (hg : Summable g)
    (hrow : ∀ i, HasSum (fun j => g (i, j)) (row i))
    (hcol : ∀ j, HasSum (fun i => g (i, j)) (col j)) :
    Summable row ∧ Summable col ∧ ∑' i, row i = ∑' j, col j := by
  have hg' : Summable (fun q : κ × ι => g q.swap) := hg.prod_symm
  have hswap : ∑' q : κ × ι, g q.swap = ∑' p : ι × κ, g p := (Equiv.prodComm κ ι).tsum_eq g
  have haCol' : HasSum (fun q : κ × ι => g q.swap) (∑' p : ι × κ, g p) := by
    rw [← hswap]; exact hg'.hasSum
  have haRow : HasSum row (∑' p, g p) := hg.hasSum.prod_fiberwise hrow
  have haCol : HasSum col (∑' p, g p) := haCol'.prod_fiberwise hcol
  exact ⟨haRow.summable, haCol.summable, haRow.tsum_eq.trans haCol.tsum_eq.symm⟩

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `T` is Hilbert–Schmidt with respect to a given Hilbert basis `d`: the squared norms of its
images on the basis vectors are summable. Basis-independent — see `isHilbertSchmidtWrt_iff`. -/
def IsHilbertSchmidtWrt {ι : Type*} (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : Prop :=
  Summable (fun i => ‖T (d i)‖ ^ 2)

/-- **The core basis-independence computation.** If `T` is Hilbert–Schmidt with respect to a
basis `d`, then its adjoint `T†` is Hilbert–Schmidt with respect to *any* basis `f`, with the same
sum of squared norms. This is what makes `IsHilbertSchmidtWrt` (and, applying this twice via
`T†† = T`, comparisons between *any* two bases for `T` itself) basis-independent. -/
theorem summable_norm_sq_adjoint_apply_and_tsum_eq {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) (hd : Summable (fun i => ‖T (d i)‖ ^ 2)) :
    Summable (fun j => ‖(ContinuousLinearMap.adjoint T) (f j)‖ ^ 2) ∧
      ∑' j, ‖(ContinuousLinearMap.adjoint T) (f j)‖ ^ 2 = ∑' i, ‖T (d i)‖ ^ 2 := by
  classical
  -- The nonnegative double family `g (i, j) := ‖⟪T dᵢ, f j⟫‖ ^ 2`.
  set g : ι × κ → ℝ := fun p => ‖(inner ℂ (T (d p.1)) (f p.2) : ℂ)‖ ^ 2 with hg_def
  have hg_nonneg : ∀ p, 0 ≤ g p := fun p => sq_nonneg _
  -- Row sums (over `j`, fixed `i`): Parseval for `f`, applied to `T dᵢ`.
  have hrow : ∀ i, HasSum (fun j => g (i, j)) (‖T (d i)‖ ^ 2) := fun i =>
    f.hasSum_norm_sq_inner (T (d i))
  -- Column sums (over `i`, fixed `j`): Parseval for `d`, applied to `T† (f j)`, after relating
  -- `⟪T dᵢ, f j⟫` to `⟪T† (f j), dᵢ⟫` via the defining property of the adjoint.
  have hcol_point : ∀ i j, g (i, j) =
      ‖(inner ℂ ((ContinuousLinearMap.adjoint T) (f j)) (d i) : ℂ)‖ ^ 2 := fun i j => by
    have heq : (inner ℂ ((ContinuousLinearMap.adjoint T) (f j)) (d i) : ℂ) =
        starRingEnd ℂ (inner ℂ (T (d i)) (f j)) := by
      rw [← ContinuousLinearMap.adjoint_inner_right T (d i) (f j)]
      exact (inner_conj_symm ((ContinuousLinearMap.adjoint T) (f j)) (d i)).symm
    rw [hg_def, heq, RCLike.norm_conj]
  have hcol : ∀ j, HasSum (fun i => g (i, j)) (‖(ContinuousLinearMap.adjoint T) (f j)‖ ^ 2) :=
    fun j => by
      simp_rw [hcol_point]
      exact d.hasSum_norm_sq_inner ((ContinuousLinearMap.adjoint T) (f j))
  -- Assemble the uncurried summability of `g` from the (nonnegative) row data.
  have hg_summable : Summable g :=
    (summable_prod_of_nonneg hg_nonneg).mpr ⟨fun i => (hrow i).summable, by
      simpa only [fun i => (hrow i).tsum_eq] using hd⟩
  obtain ⟨_, hcol_summable, heq⟩ := tsum_fiberwise_eq_of_summable hg_summable hrow hcol
  exact ⟨hcol_summable, heq.symm⟩

/-- **The same basis-independence, phrased for `T` itself rather than its adjoint.** Applying
`summable_norm_sq_adjoint_apply_and_tsum_eq` twice — once for `T`, once for `T†` — and using
`T†† = T` transports the sum of squared norms of `T` from any one basis to any other. This is
the public-facing form of the basis-independence computation: callers wanting to compare `T`
across bases (`isHilbertSchmidtWrt_iff`) should use this rather than reasoning about `T†`
directly. -/
theorem summable_norm_sq_apply_and_tsum_eq {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) (hd : Summable (fun i => ‖T (d i)‖ ^ 2)) :
    Summable (fun j => ‖T (f j)‖ ^ 2) ∧ ∑' j, ‖T (f j)‖ ^ 2 = ∑' i, ‖T (d i)‖ ^ 2 := by
  have h1 := summable_norm_sq_adjoint_apply_and_tsum_eq d f T hd
  have h2 := summable_norm_sq_adjoint_apply_and_tsum_eq f f (ContinuousLinearMap.adjoint T) h1.1
  rw [ContinuousLinearMap.adjoint_adjoint] at h2
  exact ⟨h2.1, h2.2.trans h1.2⟩

/-- **`IsHilbertSchmidtWrt` is independent of the choice of Hilbert basis.** -/
theorem isHilbertSchmidtWrt_iff {ι κ : Type*} (d : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ H)
    (T : H →L[ℂ] H) : IsHilbertSchmidtWrt d T ↔ IsHilbertSchmidtWrt f T :=
  ⟨fun hd => (summable_norm_sq_apply_and_tsum_eq d f T hd).1,
    fun hf => (summable_norm_sq_apply_and_tsum_eq f d T hf).1⟩

/-- **`T` is Hilbert–Schmidt**, independently of any particular choice of Hilbert basis. -/
def IsHilbertSchmidt (T : H →L[ℂ] H) : Prop :=
  ∃ (w : Set H) (d : HilbertBasis w ℂ H), IsHilbertSchmidtWrt d T

theorem isHilbertSchmidt_iff_isHilbertSchmidtWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) : IsHilbertSchmidt T ↔ IsHilbertSchmidtWrt d T := by
  constructor
  · rintro ⟨ι', d', hd'⟩
    exact (isHilbertSchmidtWrt_iff d' d T).mp hd'
  · intro hd
    obtain ⟨w, e, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
    exact ⟨w, e, (isHilbertSchmidtWrt_iff d e T).mp hd⟩

/-- **Accessor: an `IsHilbertSchmidt` witness gives `IsHilbertSchmidtWrt` against *any* basis.**
Lets a caller who already has a specific basis `d` in mind write `hT.isHilbertSchmidtWrt d`
instead of unfolding `isHilbertSchmidt_iff_isHilbertSchmidtWrt`. -/
theorem IsHilbertSchmidt.isHilbertSchmidtWrt {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) : IsHilbertSchmidtWrt d T :=
  (isHilbertSchmidt_iff_isHilbertSchmidtWrt d T).mp hT

/-- **Accessor: the reverse direction**, packaging `IsHilbertSchmidtWrt` evidence for one basis
into the basis-independent `IsHilbertSchmidt`. -/
theorem IsHilbertSchmidt.of_isHilbertSchmidtWrt {ι : Type*} {d : HilbertBasis ι ℂ H}
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidtWrt d T) : IsHilbertSchmidt T :=
  (isHilbertSchmidt_iff_isHilbertSchmidtWrt d T).mpr hT

/-- **Hilbert–Schmidt-ness is preserved by taking the adjoint.** A direct consequence of the
basis-independence computation: `T` being Hilbert–Schmidt with respect to `d` already gives that
`T†` is Hilbert–Schmidt with respect to that *same* `d` (no basis change needed for this
direction). -/
theorem isHilbertSchmidt_adjoint {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (ContinuousLinearMap.adjoint T) := by
  obtain ⟨w, d, hd⟩ := hT
  exact ⟨w, d, (summable_norm_sq_adjoint_apply_and_tsum_eq d d T hd).1⟩

omit [CompleteSpace H] in
/-- **Composing a Hilbert–Schmidt operator with a bounded operator on the left stays
Hilbert–Schmidt**, with respect to the same basis, by the comparison test against the operator
norm bound `‖B (T dᵢ)‖ ≤ ‖B‖ * ‖T dᵢ‖`. -/
theorem isHilbertSchmidtWrt_comp_left {ι : Type*} (d : HilbertBasis ι ℂ H) (B : H →L[ℂ] H)
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidtWrt d T) : IsHilbertSchmidtWrt d (B * T) := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_)
    (hT.mul_left (‖B‖ ^ 2))
  have hle : ‖(B * T) (d i)‖ ≤ ‖B‖ * ‖T (d i)‖ := by
    rw [mul_apply_eq_comp]
    exact B.le_opNorm (T (d i))
  calc ‖(B * T) (d i)‖ ^ 2 ≤ (‖B‖ * ‖T (d i)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = ‖B‖ ^ 2 * ‖T (d i)‖ ^ 2 := by ring

omit [CompleteSpace H] in
theorem isHilbertSchmidt_comp_left (B : H →L[ℂ] H) {T : H →L[ℂ] H}
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (B * T) := by
  obtain ⟨w, d, hd⟩ := hT
  exact ⟨w, d, isHilbertSchmidtWrt_comp_left d B hd⟩

/-- **Composing a Hilbert–Schmidt operator with a bounded operator on the right stays
Hilbert–Schmidt.** Reduced to the left-composition case via the adjoint identity
`(T * B)† = B† * T†`: `T†` is Hilbert–Schmidt (`isHilbertSchmidt_adjoint`), so `B† * T†` is
Hilbert–Schmidt (`isHilbertSchmidt_comp_left`), so its adjoint `T * B` is Hilbert–Schmidt
(`isHilbertSchmidt_adjoint` again, using `T†† = T`). -/
theorem isHilbertSchmidt_comp_right {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    (B : H →L[ℂ] H) : IsHilbertSchmidt (T * B) := by
  have hadj : IsHilbertSchmidt (ContinuousLinearMap.adjoint B * ContinuousLinearMap.adjoint T) :=
    isHilbertSchmidt_comp_left (ContinuousLinearMap.adjoint B) (isHilbertSchmidt_adjoint hT)
  have heq : ContinuousLinearMap.adjoint
      (ContinuousLinearMap.adjoint B * ContinuousLinearMap.adjoint T) = T * B := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star, star_star]
  have hadj' := isHilbertSchmidt_adjoint hadj
  rwa [heq] at hadj'

end ContinuousLinearMap
