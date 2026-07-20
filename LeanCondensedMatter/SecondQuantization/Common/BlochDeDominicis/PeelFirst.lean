import LeanCondensedMatter.SecondQuantization.Common.ExchangeCommutator
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Peeling one operator through an arbitrary-length product, via the `ζ`-commutator

The general operator-algebra step behind the finite-temperature Bloch–de Dominicis induction
(`notes/roadmaps/second-quantization.md`, and the project's physics reference notes,
`quantum-statistical-mechanics.tex`'s Bloch–De Dominicis theorem proof): generalizes
`Common/BlochDeDominicis/FourPointReduction.lean`'s hand-unrolled 3-operator peel
(`comp_comp_comp_eq_of_zetaCommutator`) to an arbitrary-length list of operators, by induction on
the list rather than by hand.

Given `C₁` and a list `l` of `(operator Bⱼ, scalar ζ-commutator coefficient cⱼ)` pairs satisfying
`[C₁, Bⱼ]_ζ = cⱼ•id` (`Common.zetaCommutator`), repeatedly rewriting `C₁Bⱼ` as `cⱼ • id + ζ•(BⱼC₁)`
and pushing `C₁` rightward through the whole list picks up one factor of `ζ` per operator it
passes, landing `C₁` at the very end:

`C₁(B₁B₂⋯Bₖ) = peelSum ζ [(B₁,c₁),…,(Bₖ,cₖ)] + ζᵏ•((B₁⋯Bₖ)C₁)`

`peelSum` depends only on `ζ` and the `(Bⱼ, cⱼ)` list — *not* on `C₁` (`C₁` appears only in `hcomm`
and on the left/right of the original operator product) — defined *recursively*, mirroring the
substitution steps directly (`peelSum ζ ((B,c) :: t) = c•(prodComp of t's operators) + ζ•(B ∘
peelSum ζ t)`), rather than as a closed `Finset.sum`-over-erasures formula matching the physics
notes' `Σⱼ ζʲc₁ⱼ⟨…Ĉⱼ…⟩` presentation directly — connecting the two is deferred to whenever the
general induction actually needs to match term-by-term against `Common.BlochDeDominicis.Pairing`.

**Pure `LinearMap` composition algebra** — no `traceFock`/KMS-rotation/`Config`-finiteness involved
here. The trace-level KMS-rotation wrapping (solving the resulting self-referential trace
equation, the way `FourPointReduction.lean` does for the 3-operator case) is done separately, in
`Common/BlochDeDominicis/PeelFirstTrace.lean`.

**`peelSum_eq_peelTerms_sum` below converts `peelSum` into a `List.sum`**, `peelTerms`'s
recursively-defined terms — not yet the indexed erasure formula (`ζʲ • cⱼ • prodComp (l.eraseIdx
j |>.map Prod.fst)`, via `List.get`/`List.eraseIdx`) that would let each term be matched
individually against `Common.BlochDeDominicis.Pairing`; that further step (`peelTerms_get`-style
API) is deferred to whenever the general induction actually needs it.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- **The composed product of a list of operators**, `B₁ ∘ B₂ ∘ ⋯ ∘ Bₖ`, right-associated with
`id` at the end of an empty list. -/
noncomputable def prodComp :
    List (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →
      AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config
  | [] => LinearMap.id
  | B :: t => B.comp (prodComp t)

@[simp] theorem prodComp_nil :
    (prodComp [] : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = LinearMap.id := rfl

theorem prodComp_cons (B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (t : List (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    prodComp (B :: t) = B.comp (prodComp t) := rfl

/-- **The recursive "peeled" sum**: mirrors the exact substitution steps of pushing `C₁`
rightward through a list of `(operator, scalar ζ-commutator coefficient)` pairs one at a time.
Depends only on `ζ` and the list — not on `C₁`. -/
noncomputable def peelSum (ζ : ℂ) :
    List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ) →
      AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config
  | [] => 0
  | (B, c) :: t => c • prodComp (t.map Prod.fst) + ζ • (B.comp (peelSum ζ t))

/-- **The individual terms `peelSum` sums**, one per position in `l`, in order: at position `j`
(0-indexed), the term is `ζ^j·cⱼ•(remaining product with `Bⱼ` erased)`. Defined recursively in
lockstep with `peelSum` itself, so `peelSum_eq_peelTerms_sum` below is close to definitional. -/
noncomputable def peelTerms (ζ : ℂ) :
    List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ) →
      List (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
  | [] => []
  | (B, c) :: t => (c • prodComp (t.map Prod.fst)) :: (peelTerms ζ t).map (fun x => ζ • (B.comp x))

/-- **`peelSum` is the sum of its `peelTerms`** — the closed-form counterpart of `peelSum`'s
recursive definition, `Σⱼ ζʲcⱼ•(remaining product with `Bⱼ` erased)` as a `List.sum` rather than
an index/`Finset.sum`-over-erasures formula (`l.get`/`l.eraseIdx`) matching the physics notes'
`Σⱼ ζʲc₁ⱼ⟨…Ĉⱼ…⟩` presentation letter-for-letter — connecting `peelTerms` to that indexed form,
whenever the general induction needs to match term-by-term against
`Common.BlochDeDominicis.Pairing`, is deferred. -/
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
theorem comp_prodComp_eq_of_zetaCommutator (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hcomm : ∀ p ∈ l, zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    C1.comp (prodComp (l.map Prod.fst)) =
      peelSum ζ l + ζ ^ l.length • ((prodComp (l.map Prod.fst)).comp C1) := by
  induction l with
  | nil => simp [peelSum]
  | cons p t ih =>
    have hp : ∀ x, C1 (p.1 x) = p.2 • x + ζ • p.1 (C1 x) := by
      intro x
      have h := DFunLike.congr_fun (hcomm p (List.mem_cons_self ..)) x
      simp only [zetaCommutator, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.id_apply] at h
      rwa [sub_eq_iff_eq_add] at h
    have ihp := ih (fun q hq => hcomm q (List.mem_cons_of_mem p hq))
    apply LinearMap.ext
    intro x
    have hihp := DFunLike.congr_fun ihp x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at hihp
    simp only [List.map_cons, List.length_cons, prodComp_cons, peelSum, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.smul_apply]
    rw [hp (prodComp (t.map Prod.fst) x), hihp]
    simp only [map_add, map_smul, smul_add, smul_smul, pow_succ]
    module

end Common
end SecondQuantization
