import LeanCondensedMatter.Analysis.ScalarExchange.Basic
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Peeling one operator through a product with a `ζ`-commutator

Suppose `C₁` and operators `Bⱼ` satisfy scalar exchange relations
`[C₁, Bⱼ]_ζ = cⱼ • id`. Repeatedly moving `C₁` through an ordered product gives

`C₁(B₁⋯Bₖ) = peelSum ζ [(B₁,c₁),…,(Bₖ,cₖ)] + ζᵏ • ((B₁⋯Bₖ)C₁)`.

The recursively defined `peelSum` records the contribution created each time the distinguished
operator crosses one factor. `PeelTermsIndexed` identifies this recursive expression with the
position-indexed erase-one-factor formula used in pairing arguments.

Everything in this module is pure `LinearMap` composition algebra. Trace cyclicity, KMS rotation,
summability, and configuration finiteness enter only in the separate trace-level specialization.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- **The recursive "peeled" sum**: mirrors the exact substitution steps of pushing `C₁`
rightward through a list of `(operator, scalar ζ-commutator coefficient)` pairs one at a time.
Depends only on `ζ` and the list — not on `C₁`. -/
noncomputable def peelSum (ζ : ℂ) :
    List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ) →
      AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config
  | [] => 0
  | (B, c) :: t =>
      c • (t.map Prod.fst).prod + ζ • (B.comp (peelSum ζ t))

/-- **The individual terms `peelSum` sums**, one per position in `l`, in order: at position `j`
(0-indexed), the term is `ζ^j·cⱼ•(remaining product with Bⱼ erased)`. Defined recursively in
lockstep with `peelSum` itself, so `peelSum_eq_peelTerms_sum` below is close to definitional. -/
noncomputable def peelTerms (ζ : ℂ) :
    List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ) →
      List (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
  | [] => []
  | (B, c) :: t =>
      (c • (t.map Prod.fst).prod) :: (peelTerms ζ t).map (fun x => ζ • (B.comp x))

/-- **`peelSum` is the sum of its `peelTerms`** — the closed-form counterpart of `peelSum`'s
recursive definition, `Σⱼ ζʲcⱼ•(remaining product with Bⱼ erased)` as a `List.sum` rather than
an index/`Finset.sum`-over-erasures formula (`l.eraseIdx`) matching the physics notes'
`Σⱼ ζʲc₁ⱼ⟨…Ĉⱼ…⟩` presentation letter-for-letter (`PeelTermsIndexed.lean`'s `peelTerms_eq_ofFn`
gives that indexed form). -/
theorem peelSum_eq_peelTerms_sum (ζ : ℂ)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ)) :
    peelSum ζ l = (peelTerms ζ l).sum := by
  induction l with
  | nil => simp [peelSum, peelTerms]
  | cons p t ih =>
    obtain ⟨B, c⟩ := p
    have hmap : ∀ l' : List (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config),
        (l'.map (fun x => ζ • (B.comp x))).sum = ζ • (B.comp l'.sum) := by
      intro l'
      induction l' with
      | nil => simp
      | cons x t' ih' => simp [List.sum_cons, ih', LinearMap.comp_add, smul_add]
    simp only [peelSum, peelTerms, List.sum_cons, hmap, ih]

/-- **Peeling `C₁` through an arbitrary-length product**: repeatedly rewriting `C₁Bⱼ` via each
pair's `ζ`-commutator coefficient and pushing `C₁` rightward, `C₁` lands at the very end having
picked up `ζ^{l.length}`. -/
theorem comp_prod_eq_of_zetaCommutator (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hcomm : ∀ p ∈ l, ScalarExchange.zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    C1.comp ((l.map Prod.fst).prod) =
      peelSum ζ l + ζ ^ l.length • ((l.map Prod.fst).prod.comp C1) := by
  induction l with
  | nil =>
      simp [peelSum, Module.End.one_eq_id]
  | cons p t ih =>
    have hp : ∀ x, C1 (p.1 x) = p.2 • x + ζ • p.1 (C1 x) := by
      intro x
      have h := DFunLike.congr_fun (hcomm p (List.mem_cons_self ..)) x
      change C1 (p.1 x) - ζ • p.1 (C1 x) = p.2 • x at h
      exact (sub_eq_iff_eq_add).mp h
    have ihp := ih (fun q hq => hcomm q (List.mem_cons_of_mem p hq))
    apply LinearMap.ext
    intro x
    have hihp := DFunLike.congr_fun ihp x
    simp only [List.map_cons, List.length_cons, List.prod_cons, Module.End.mul_eq_comp, peelSum,
      LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at hihp ⊢
    rw [hp ((t.map Prod.fst).prod x), hihp]
    simp only [map_add, map_smul, smul_add, smul_smul, pow_succ]
    module

end Common
end SecondQuantization
