import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite scalar-exchange peel for linear endomorphisms

Repeatedly applies a supplied scalar exchange relation through an ordered finite product of
endomorphisms. The construction depends only on the exchange relation itself, not on a commutator
presentation or any second-quantized model.
-/

namespace LinearMap

/-- The exchange terms generated while pushing one labelled endomorphism through a finite tail. -/
noncomputable def operatorPeelSum {Label M : Type*} [AddCommMonoid M] [Module ℂ M]
    (operator : Label → M →ₗ[ℂ] M) (exchangeCoeff : Label → Label → ℂ)
    (ζ : ℂ) (C : Label) : List Label → M →ₗ[ℂ] M
  | [] => 0
  | D :: t =>
      exchangeCoeff C D • (t.map operator).prod +
        ζ • ((operator D).comp (operatorPeelSum operator exchangeCoeff ζ C t))

@[simp]
theorem operatorPeelSum_nil {Label M : Type*} [AddCommMonoid M] [Module ℂ M]
    (operator : Label → M →ₗ[ℂ] M) (exchangeCoeff : Label → Label → ℂ)
    (ζ : ℂ) (C : Label) :
    operatorPeelSum operator exchangeCoeff ζ C [] = 0 := rfl

/-- Repeatedly apply a scalar exchange relation while pushing one endomorphism through a finite
ordered product. -/
theorem operator_comp_prod_eq_operatorPeelSum
    {Label M : Type*} [AddCommMonoid M] [Module ℂ M]
    (operator : Label → M →ₗ[ℂ] M) (exchangeCoeff : Label → Label → ℂ) (ζ : ℂ)
    (hExchange : ∀ C D,
      (operator C).comp (operator D) =
        exchangeCoeff C D • (LinearMap.id : M →ₗ[ℂ] M) +
          ζ • ((operator D).comp (operator C)))
    (C : Label) (l : List Label) :
    (operator C).comp ((l.map operator).prod) =
      operatorPeelSum operator exchangeCoeff ζ C l +
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

end LinearMap
