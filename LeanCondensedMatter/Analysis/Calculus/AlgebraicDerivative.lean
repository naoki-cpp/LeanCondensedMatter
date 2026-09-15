import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Weak algebraic derivatives

A family valued in an algebraic complex vector space has an algebraic derivative when every
complex-linear scalar functional sees the corresponding ordinary complex derivative. This gives a
calculus for vector spaces with no chosen topology.
-/

open scoped BigOperators

variable {V W : Type*}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

/-- Weak derivative for a family valued in an algebraic complex vector space.

No topology is imposed on `V`. Instead, every algebraic complex-linear functional `V →ₗ[ℂ] ℂ`
must turn the family into an ordinarily complex-differentiable scalar function with the stated
derivative. -/
def HasAlgebraicDerivAt (F : ℂ → V) (F' : V) (A : ℂ) : Prop :=
  ∀ ℓ : V →ₗ[ℂ] ℂ, HasDerivAt (fun z => ℓ (F z)) (ℓ F') A

/-- A scalar differentiable coefficient multiplying a fixed algebraic vector has the expected
algebraic derivative. -/
theorem hasAlgebraicDerivAt_smul_const {f : ℂ → ℂ} {f' A : ℂ}
    (hf : HasDerivAt f f' A) (v : V) :
    HasAlgebraicDerivAt (fun z => f z • v) (f' • v) A := by
  intro ℓ
  simpa only [map_smul] using hf.smul_const (ℓ v)

namespace HasAlgebraicDerivAt

/-- Algebraic derivatives are additive. -/
theorem add {F G : ℂ → V} {F' G' : V} {A : ℂ}
    (hF : HasAlgebraicDerivAt F F' A) (hG : HasAlgebraicDerivAt G G' A) :
    HasAlgebraicDerivAt (fun z => F z + G z) (F' + G') A := by
  intro ℓ
  simp only [map_add]
  apply ((hF ℓ).add (hG ℓ)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- A complex-linear map transports algebraic derivatives. -/
theorem map {F : ℂ → V} {F' : V} {A : ℂ}
    (hF : HasAlgebraicDerivAt F F' A) (T : V →ₗ[ℂ] W) :
    HasAlgebraicDerivAt (fun z => T (F z)) (T F') A := by
  intro ℓ
  simpa only [LinearMap.comp_apply] using hF (ℓ.comp T)

/-- Multiplying an algebraic-vector-valued family by a constant scalar multiplies its derivative. -/
theorem const_smul {F : ℂ → V} {F' : V} {A : ℂ}
    (hF : HasAlgebraicDerivAt F F' A) (c : ℂ) :
    HasAlgebraicDerivAt (fun z => c • F z) (c • F') A := by
  intro ℓ
  simpa only [map_smul, smul_eq_mul] using (hF ℓ).const_mul c

/-- Reparametrizing an algebraic-vector-valued family by a scalar differentiable map obeys the
chain rule. -/
theorem comp {F : ℂ → V} {F' : V} {g : ℂ → ℂ} {g' A : ℂ}
    (hF : HasAlgebraicDerivAt F F' (g A)) (hg : HasDerivAt g g' A) :
    HasAlgebraicDerivAt (fun z => F (g z)) (g' • F') A := by
  intro ℓ
  have hcomp := HasDerivAt.comp A (hF ℓ) hg
  have hcomp' : HasDerivAt (fun z => ℓ (F (g z))) (ℓ F' * g') A := by
    apply hcomp.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun _ => rfl)
  simpa only [map_smul, smul_eq_mul, mul_comm] using hcomp'

/-- Finite sums preserve algebraic derivatives. -/
theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℂ → V} {F' : ι → V} {A : ℂ}
    (hF : ∀ i ∈ s, HasAlgebraicDerivAt (F i) (F' i) A) :
    HasAlgebraicDerivAt (fun z => ∑ i ∈ s, F i z) (∑ i ∈ s, F' i) A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro ℓ
      simpa using (hasDerivAt_const (x := A) (c := (0 : ℂ)))
  | @insert a s ha ih =>
      have ha' := hF a (Finset.mem_insert_self a s)
      have hs' := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      simpa only [Finset.sum_insert ha] using ha'.add hs'

end HasAlgebraicDerivAt
