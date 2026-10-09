import LeanCondensedMatter.Analysis.ScalarExchange.Peel
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Peeling one operator through a product with a `ζ`-commutator

Suppose `C₁` and operators `Bⱼ` satisfy scalar exchange relations
`[C₁, Bⱼ]_ζ = cⱼ • id`. Repeatedly moving `C₁` through an ordered product gives

`C₁(B₁⋯Bₖ) = ScalarExchange.peelSumWithCoefficients ζ [(B₁,c₁),…,(Bₖ,cₖ)] + ζᵏ • ((B₁⋯Bₖ)C₁)`.

The recursively defined `ScalarExchange.peelSumWithCoefficients` records the contribution
created each time the distinguished operator crosses one factor.
`ScalarExchange.peelSumWithCoefficients_eq_sum` gives the position-indexed erase-one-factor
formula used in pairing arguments.

The coefficient-paired recursion is shared with `Analysis.ScalarExchange.Peel`. This module keeps
the commutator-form adapter. Trace cyclicity, KMS rotation, summability,
and configuration finiteness enter only in the separate trace-level specialization.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- **Peeling `C₁` through an arbitrary-length product**: repeatedly rewriting `C₁Bⱼ` via each
pair's `ζ`-commutator coefficient and pushing `C₁` rightward, `C₁` lands at the very end having
picked up `ζ^{l.length}`. -/
theorem comp_prod_eq_of_zetaCommutator (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hcomm : ∀ p ∈ l, ScalarExchange.zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    C1.comp ((l.map Prod.fst).prod) =
      ScalarExchange.peelSumWithCoefficients ζ l + ζ ^ l.length • ((l.map Prod.fst).prod.comp C1) := by
  have hExchange : ∀ p ∈ l,
      C1 * p.1 = p.2 • (1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) +
        ζ • (p.1 * C1) := by
    intro p hp
    have hcomm' : C1 * p.1 - ζ • (p.1 * C1) =
        p.2 • (1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
      simpa only [ScalarExchange.zetaCommutator, Module.End.mul_eq_comp,
        Module.End.one_eq_id] using hcomm p hp
    exact (sub_eq_iff_eq_add).mp hcomm'
  have h := ScalarExchange.mul_prod_eq_peelSumWithCoefficients ζ C1 l hExchange
  simpa only [Module.End.mul_eq_comp, Module.End.one_eq_id] using h

end Common
end SecondQuantization
