import LeanCondensedMatter.Analysis.CompactSelfAdjoint
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

/-- **`IsHilbertSchmidtWrt` is independent of the choice of Hilbert basis.** Applying
`summable_norm_sq_adjoint_apply_and_tsum_eq` twice — once for `T`, once for `T†` — and using
`T†† = T` transports Hilbert–Schmidt-ness (and the common sum of squared norms) from any one
basis to any other. -/
theorem isHilbertSchmidtWrt_iff {ι κ : Type*} (d : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ H)
    (T : H →L[ℂ] H) : IsHilbertSchmidtWrt d T ↔ IsHilbertSchmidtWrt f T := by
  constructor
  · intro hd
    have h1 := summable_norm_sq_adjoint_apply_and_tsum_eq d f T hd
    have h2 := summable_norm_sq_adjoint_apply_and_tsum_eq f f
      (ContinuousLinearMap.adjoint T) h1.1
    rw [ContinuousLinearMap.adjoint_adjoint] at h2
    exact h2.1
  · intro hf
    have h1 := summable_norm_sq_adjoint_apply_and_tsum_eq f d T hf
    have h2 := summable_norm_sq_adjoint_apply_and_tsum_eq d d
      (ContinuousLinearMap.adjoint T) h1.1
    rw [ContinuousLinearMap.adjoint_adjoint] at h2
    exact h2.1

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

end ContinuousLinearMap
