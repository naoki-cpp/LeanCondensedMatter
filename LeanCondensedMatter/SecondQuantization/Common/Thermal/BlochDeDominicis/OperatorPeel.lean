import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Generic operator peel identity

The first algebraic step in a Bloch–de Dominicis recursion is independent of the Gibbs state: move
the leading operator through a finite tail using a scalar exchange relation. This file packages that
step for linear endomorphisms of an arbitrary complex module.

If

`C D = contraction(C,D) I + ζ D C`,

then repeated exchange gives

`C (D₁⋯Dₖ) = peel(C; D₁,…,Dₖ) + ζ^k (D₁⋯Dₖ) C`.

The subsequent KMS rotation and analytic summability belong to the statistics-specific thermal
implementation.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

noncomputable section

variable {Label M : Type*} [AddCommMonoid M] [Module ℂ M]

/-- Right-associated product of a list of labeled linear endomorphisms. -/
noncomputable def operatorProduct (operator : Label → M →ₗ[ℂ] M) :
    List Label → M →ₗ[ℂ] M
  | [] => LinearMap.id
  | C :: t => (operator C).comp (operatorProduct operator t)

@[simp]
theorem operatorProduct_nil (operator : Label → M →ₗ[ℂ] M) :
    operatorProduct operator [] = LinearMap.id := rfl

@[simp]
theorem operatorProduct_cons (operator : Label → M →ₗ[ℂ] M)
    (C : Label) (t : List Label) :
    operatorProduct operator (C :: t) =
      (operator C).comp (operatorProduct operator t) := rfl

/-- Products respect list concatenation. -/
theorem operatorProduct_append (operator : Label → M →ₗ[ℂ] M)
    (l₁ l₂ : List Label) :
    operatorProduct operator (l₁ ++ l₂) =
      (operatorProduct operator l₁).comp (operatorProduct operator l₂) := by
  induction l₁ with
  | nil => simp
  | cons C t ih =>
      rw [List.cons_append, operatorProduct_cons, operatorProduct_cons, ih,
        LinearMap.comp_assoc]

/-- The contraction terms generated while pushing a leading operator through a finite tail. -/
noncomputable def operatorPeelSum (operator : Label → M →ₗ[ℂ] M)
    (contraction : Label → Label → ℂ) (ζ : ℂ) (C : Label) :
    List Label → M →ₗ[ℂ] M
  | [] => 0
  | D :: t =>
      contraction C D • operatorProduct operator t +
        ζ • ((operator D).comp (operatorPeelSum operator contraction ζ C t))

@[simp]
theorem operatorPeelSum_nil (operator : Label → M →ₗ[ℂ] M)
    (contraction : Label → Label → ℂ) (ζ : ℂ) (C : Label) :
    operatorPeelSum operator contraction ζ C [] = 0 := rfl

/-- Repeated scalar exchange through an arbitrary tail. -/
theorem operator_comp_operatorProduct_eq_operatorPeelSum
    (operator : Label → M →ₗ[ℂ] M) (contraction : Label → Label → ℂ) (ζ : ℂ)
    (hExchange : ∀ C D,
      (operator C).comp (operator D) =
        contraction C D • (LinearMap.id : M →ₗ[ℂ] M) +
          ζ • ((operator D).comp (operator C)))
    (C : Label) (l : List Label) :
    (operator C).comp (operatorProduct operator l) =
      operatorPeelSum operator contraction ζ C l +
        ζ ^ l.length • ((operatorProduct operator l).comp (operator C)) := by
  induction l with
  | nil =>
      simp [operatorPeelSum]
  | cons D t ih =>
      apply LinearMap.ext
      intro x
      have hexchange := DFunLike.congr_fun (hExchange C D) (operatorProduct operator t x)
      have hih := DFunLike.congr_fun ih x
      simp only [operatorProduct_cons, operatorPeelSum, List.length_cons,
        LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at hexchange hih ⊢
      rw [hexchange, hih]
      simp only [map_add, map_smul, pow_succ]
      module

end
end BlochDeDominicis
end Common
end SecondQuantization
