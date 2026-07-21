import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelFirst
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# `peelTerms`, reindexed by position (`List.eraseIdx`) instead of built recursively

`PeelFirst.lean`'s `peelTerms` is defined recursively, in lockstep with `peelSum`;
`peelTerms_eq_ofFn` below shows it agrees with the "closed-form", indexed description used by the
physics reference notes' `Σⱼ ζʲc₁ⱼ⟨…Ĉⱼ…⟩` presentation: at position `j` (0-indexed), the term is
`ζʲ • cⱼ • (the remaining product with the `j`-th operator erased)`, expressed through
`List.eraseIdx`.

This is a `List`-level statement, in the same "erase one position from a flat list" shape as
`peelTerms` itself — `Common/BlochDeDominicis/Induction.lean` connects it to
`Combinatorics/PerfectPairing.lean`'s `Fin (2n)`-indexed `Pairing.eraseZeroPair` (a different
erasure/reindexing scheme, built for pairs rather than single positions).
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- **`peelTerms`'s `j`-th term, in closed form**: `ζʲ • cⱼ • (remaining product with the `j`-th
operator erased)`, matching the physics reference notes' `Σⱼ ζʲc₁ⱼ⟨…Ĉⱼ…⟩` presentation
term-by-term. -/
theorem peelTerms_eq_ofFn (ζ : ℂ)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ)) :
    peelTerms ζ l =
      List.ofFn (fun j : Fin l.length =>
        ζ ^ (j : ℕ) • (l[(j : ℕ)]'j.isLt).2 • prodComp ((l.eraseIdx j).map Prod.fst)) := by
  induction l with
  | nil => simp [peelTerms]
  | cons p t ih =>
    obtain ⟨B, c⟩ := p
    rw [List.ofFn_succ, peelTerms]
    simp only [Fin.val_zero, pow_zero, one_smul, List.getElem_cons_zero, List.eraseIdx_cons_zero]
    congr 1
    rw [ih, List.map_ofFn]
    congr 1
    funext i
    change ζ • (B.comp
        (ζ ^ (i : ℕ) • (t[(i : ℕ)]'i.isLt).2 • prodComp ((t.eraseIdx i).map Prod.fst))) =
      ζ ^ ((i.succ : Fin (t.length + 1)) : ℕ) •
          ((((B, c) :: t))[((i.succ : Fin (t.length + 1)) : ℕ)]'
            (i.succ : Fin (t.length + 1)).isLt).2 •
        prodComp ((((B, c) :: t).eraseIdx (i.succ : Fin (t.length + 1))).map Prod.fst)
    simp only [Fin.val_succ, List.getElem_cons_succ, List.eraseIdx_cons_succ, List.map_cons,
      prodComp_cons, pow_succ, LinearMap.comp_smul, smul_smul]
    congr 1
    ring

end Common
end SecondQuantization
