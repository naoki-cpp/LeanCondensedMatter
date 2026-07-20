import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelFirst

set_option linter.style.header false

/-!
# `PeelFirst.lean`'s `prodComp`, indexed by a `Fin k`-family instead of a `List`

A small bridging piece toward the general `n`-point Bloch–de Dominicis induction
(`notes/roadmaps/second-quantization.md`'s Phase 9): the eventual induction states the `2n`
operators as a family `C : Fin (2 * n) → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config` (to match
`Common.BlochDeDominicis.Pairing n`'s own `Fin (2 * n)`-indexing), while `PeelFirst.lean`'s
`comp_prodComp_eq_of_zetaCommutator` and `PeelFirstTrace.lean`'s/`GibbsExpectation.lean`'s wrappers
around it are stated over `List`s. `prodCompFamily` is `prodComp` composed with `List.ofFn`, and
`prodCompFamily_succ` (via Lean core's `List.ofFn_succ`) unfolds it one operator at a time —
letting a family-indexed statement invoke the `List`-indexed peel lemmas directly on `C 0` and the
tail family `fun i => C i.succ`, the way the induction's base step needs.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- **The composed product of a `Fin k`-indexed operator family**, `C 0 ∘ C 1 ∘ ⋯ ∘ C (k-1)`, via
`PeelFirst.lean`'s `prodComp` applied to `List.ofFn C`. -/
noncomputable def prodCompFamily {k : ℕ}
    (C : Fin k → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  prodComp (List.ofFn C)

theorem prodCompFamily_succ {k : ℕ}
    (C : Fin (k + 1) → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    prodCompFamily C = (C 0).comp (prodCompFamily fun i : Fin k => C i.succ) := by
  rw [prodCompFamily, prodCompFamily, List.ofFn_succ, prodComp_cons]

end Common
end SecondQuantization
