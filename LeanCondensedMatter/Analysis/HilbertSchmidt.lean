import LeanCondensedMatter.Analysis.TraceClassOps
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Hilbert–Schmidt operators

Defines the Hilbert–Schmidt class of (possibly non-self-adjoint) bounded operators on a Hilbert
space, and proves the fundamental basis-independence fact that makes it well-defined:
`Σᵢ ‖T dᵢ‖²` has the same value (finite or not) for every Hilbert basis `d`.

**Motivation.** `ContinuousLinearMap.trace` (`Analysis/CompactSelfAdjoint.lean`) is only defined
for compact self-adjoint trace-class operators. The Born-rule probability `Tr[E_m ρ]` needs a
trace for `E_m ∘ ρ`, which need not be self-adjoint even when `E_m` and `ρ` both are (a product
of self-adjoint operators is self-adjoint only when they commute). The standard fix: if `S`, `T`
are both Hilbert–Schmidt, `S† ∘ T` is trace-class regardless of self-adjointness, with
`Tr[S† ∘ T] = Σᵢ ⟪S dᵢ, T dᵢ⟫` well-defined via the Hilbert–Schmidt inner product. This file lays
the groundwork: the Hilbert–Schmidt predicate and its basis-independence. See
`notes/roadmaps/operator-algebra.md`.
-/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `T` is Hilbert–Schmidt with respect to a given Hilbert basis `d`: the squared norms of its
images on the basis vectors are summable. Basis-independent — see
`summable_norm_sq_apply_iff_summable_norm_sq_adjoint_apply` and
`isHilbertSchmidtWrt_iff_forall`. -/
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
  -- Swap to the column-first form to read off the conclusion.
  have hg_summable' : Summable (fun q : κ × ι => g q.swap) := hg_summable.prod_symm
  have hcol_prod := (summable_prod_of_nonneg
    (f := fun q : κ × ι => g q.swap) (fun q => hg_nonneg q.swap)).mp hg_summable'
  have hcol_summable : Summable (fun j => ‖(ContinuousLinearMap.adjoint T) (f j)‖ ^ 2) :=
    hcol_prod.2.congr fun j => (hcol j).tsum_eq
  refine ⟨hcol_summable, ?_⟩
  have hswap : ∑' q : κ × ι, g q.swap = ∑' p : ι × κ, g p :=
    (Equiv.prodComm κ ι).tsum_eq g
  calc ∑' j, ‖(ContinuousLinearMap.adjoint T) (f j)‖ ^ 2
      = ∑' j, ∑' i, g (i, j) := tsum_congr fun j => ((hcol j).tsum_eq).symm
    _ = ∑' q : κ × ι, g q.swap := (Summable.tsum_prod' hg_summable'
        (fun j => (hcol_prod.1 j))).symm
    _ = ∑' p : ι × κ, g p := hswap
    _ = ∑' i, ∑' j, g (i, j) := Summable.tsum_prod' hg_summable (fun i => (hrow i).summable)
    _ = ∑' i, ‖T (d i)‖ ^ 2 := tsum_congr fun i => (hrow i).tsum_eq

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

/-- **The core Fubini computation underlying basis-independence of `innerHS`.** For `S`, `T`
Hilbert–Schmidt with respect to a basis `d`, and *any* other basis `f`, the double sum
`Σᵢⱼ ⟪S dᵢ, fⱼ⟫ ⟪fⱼ, T dᵢ⟫` can be summed either row-first (giving `Σᵢ ⟪S dᵢ, T dᵢ⟫`, via the
resolution of the identity along `f`) or column-first (giving `Σⱼ ⟪T† fⱼ, S† fⱼ⟫`, via the
resolution of the identity along `d`, after rewriting each factor with the adjoint). Unlike the
squared-norm swap used for `IsHilbertSchmidtWrt` basis-independence, the summands here are complex
(not nonnegative), so absolute summability of the double family is established via the AM–GM
bound `|ab| ≤ (|a|² + |b|²) / 2` instead of `summable_prod_of_nonneg` applied to the family
itself. -/
theorem hasSum_inner_swap {ι κ : Type*} (d : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ H)
    {S T : H →L[ℂ] H} (hSd : IsHilbertSchmidtWrt d S) (hTd : IsHilbertSchmidtWrt d T) :
    Summable (fun j => (inner ℂ (ContinuousLinearMap.adjoint T (f j))
        (ContinuousLinearMap.adjoint S (f j)) : ℂ)) ∧
      ∑' j, (inner ℂ (ContinuousLinearMap.adjoint T (f j))
          (ContinuousLinearMap.adjoint S (f j)) : ℂ) =
        ∑' i, (inner ℂ (S (d i)) (T (d i)) : ℂ) := by
  classical
  set g : ι × κ → ℂ :=
    fun p => (inner ℂ (S (d p.1)) (f p.2) : ℂ) * (inner ℂ (f p.2) (T (d p.1)) : ℂ) with hg_def
  -- Absolute summability of `g`, via the AM–GM bound on each term.
  set bd : ι × κ → ℝ :=
    fun p => (‖(inner ℂ (S (d p.1)) (f p.2) : ℂ)‖ ^ 2 +
      ‖(inner ℂ (f p.2) (T (d p.1)) : ℂ)‖ ^ 2) / 2 with hbd_def
  have hbd_nonneg : ∀ p, 0 ≤ bd p := fun p => by positivity
  have hg_le : ∀ p, ‖g p‖ ≤ bd p := fun p => by
    rw [hg_def, hbd_def]
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
  have hg_summable : Summable g := Summable.of_norm_bounded hbd_summable hg_le
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
  -- Assemble both iterated sums against the *same* total `∑' p, g p`, via `HasSum.prod_fiberwise`
  -- (valid for general, not-necessarily-nonnegative summable families).
  have hg_summable' : Summable (fun q : κ × ι => g q.swap) := hg_summable.prod_symm
  have hswap_eq : ∑' q : κ × ι, g q.swap = ∑' p : ι × κ, g p := (Equiv.prodComm κ ι).tsum_eq g
  have ha' : HasSum (fun q : κ × ι => g q.swap) (∑' p : ι × κ, g p) :=
    hswap_eq ▸ hg_summable'.hasSum
  have hcolSum : HasSum (fun j => (inner ℂ (ContinuousLinearMap.adjoint T (f j))
      (ContinuousLinearMap.adjoint S (f j)) : ℂ)) (∑' p : ι × κ, g p) :=
    ha'.prod_fiberwise hcol
  have ha : HasSum g (∑' p : ι × κ, g p) := hg_summable.hasSum
  have hrowSum : HasSum (fun i => (inner ℂ (S (d i)) (T (d i)) : ℂ)) (∑' p : ι × κ, g p) :=
    ha.prod_fiberwise hrow
  exact ⟨hcolSum.summable, hcolSum.tsum_eq.trans hrowSum.tsum_eq.symm⟩

/-- **`innerHS` is independent of the choice of Hilbert basis.** Applying
`hasSum_inner_swap` with the same basis for both arguments identifies `innerHS d S T` with
`Σᵢ ⟪T† dᵢ, S† dᵢ⟫`; applying it again with `d` and `f` swapped identifies the latter with
`innerHS f S T`. -/
theorem innerHS_eq_of_isHilbertSchmidt {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : innerHS d S T = innerHS f S T := by
  have hSd := (isHilbertSchmidt_iff_isHilbertSchmidtWrt d S).mp hS
  have hTd := (isHilbertSchmidt_iff_isHilbertSchmidtWrt d T).mp hT
  have hSf := (isHilbertSchmidt_iff_isHilbertSchmidtWrt f S).mp hS
  have hTf := (isHilbertSchmidt_iff_isHilbertSchmidtWrt f T).mp hT
  have h2 := hasSum_inner_swap d d hSd hTd
  have h3 := hasSum_inner_swap f d hSf hTf
  exact h2.2.symm.trans h3.2

/-- **Reconciliation with `ContinuousLinearMap.trace`.** For a compact self-adjoint trace-class
`A`, the Hilbert–Schmidt inner product `innerHS d 1 A` — i.e. `Σᵢ ⟪dᵢ, A dᵢ⟫`, computed with `S`
taken to be the identity — agrees with `trace hAtc` (cast to `ℂ`). This is Track C's step 4
(`notes/roadmaps/operator-algebra.md`): it identifies the Hilbert–Schmidt route to a trace (needed
for the Born rule, where the relevant operator need not be self-adjoint) with the eigenvalue-sum
`trace` already defined for the self-adjoint case, on their common domain of applicability. -/
theorem innerHS_one_eq_trace {A : H →L[ℂ] H} (hAcpt : IsCompactOperator A) (hAsym : A.IsSymmetric)
    (hAtc : IsTraceClass A) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    innerHS d 1 A = (trace hAtc : ℂ) := by
  have hone : (fun i => (inner ℂ ((1 : H →L[ℂ] H) (d i)) (A (d i)) : ℂ)) =
      (fun i => (inner ℂ (d i) (A (d i)) : ℂ)) := by
    funext i
    rw [one_apply_eq_self]
  have hreal : ∀ i, (((inner ℂ (d i) (A (d i)) : ℂ)).re : ℂ) = (inner ℂ (d i) (A (d i)) : ℂ) :=
    fun i => by
      have hconj : starRingEnd ℂ (inner ℂ (d i) (A (d i)) : ℂ) = (inner ℂ (d i) (A (d i)) : ℂ) := by
        rw [inner_conj_symm]
        exact hAsym (d i) (d i)
      exact Complex.conj_eq_iff_re.mp hconj
  have hcast := (hasSum_inner_apply_eq_trace hAcpt hAsym hAtc d).mapL Complex.ofRealCLM
  simp only [Complex.ofRealCLM_apply] at hcast
  simp_rw [hreal] at hcast
  unfold innerHS
  rw [hone]
  exact hcast.tsum_eq

end ContinuousLinearMap
