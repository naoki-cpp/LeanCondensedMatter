import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Generic operator peel identity

Repeatedly applies `C D = contraction(C,D) I + ζ D C` through a finite operator tail. Gibbs/KMS
structure belongs downstream. Ordered operator lists use Mathlib's canonical `List.prod` on
endomorphisms, whose multiplication is composition.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

noncomputable section

variable {Label M : Type*} [AddCommMonoid M] [Module ℂ M]

/-- The contraction terms generated while pushing a leading operator through a finite tail. -/
noncomputable def operatorPeelSum (operator : Label → M →ₗ[ℂ] M)
    (contraction : Label → Label → ℂ) (ζ : ℂ) (C : Label) :
    List Label → M →ₗ[ℂ] M
  | [] => 0
  | D :: t =>
      contraction C D • (t.map operator).prod +
        ζ • ((operator D).comp (operatorPeelSum operator contraction ζ C t))

@[simp]
theorem operatorPeelSum_nil (operator : Label → M →ₗ[ℂ] M)
    (contraction : Label → Label → ℂ) (ζ : ℂ) (C : Label) :
    operatorPeelSum operator contraction ζ C [] = 0 := rfl

/-- Repeated scalar exchange through an arbitrary tail. -/
theorem operator_comp_prod_eq_operatorPeelSum
    (operator : Label → M →ₗ[ℂ] M) (contraction : Label → Label → ℂ) (ζ : ℂ)
    (hExchange : ∀ C D,
      (operator C).comp (operator D) =
        contraction C D • (LinearMap.id : M →ₗ[ℂ] M) +
          ζ • ((operator D).comp (operator C)))
    (C : Label) (l : List Label) :
    (operator C).comp ((l.map operator).prod) =
      operatorPeelSum operator contraction ζ C l +
        ζ ^ l.length • ((l.map operator).prod.comp (operator C)) := by
  induction l with
  | nil =>
      simp [operatorPeelSum, Module.End.one_eq_id]
  | cons D t ih =>
      apply LinearMap.ext
      intro x
      have hexchange := DFunLike.congr_fun (hExchange C D) ((t.map operator).prod x)
      have hih := DFunLike.congr_fun ih x
      simp only [List.map_cons, List.prod_cons, Module.End.mul_eq_comp, operatorPeelSum,
        List.length_cons, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hexchange hih ⊢
      rw [hexchange, hih]
      simp only [map_add, map_smul, pow_succ]
      module

end
end BlochDeDominicis
end Common
end SecondQuantization
