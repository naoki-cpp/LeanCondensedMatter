import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

set_option linter.style.header false

/-!
# Scalar exchange algebra

This module owns the representation-independent algebra behind fixed-sign exchange relations.

For an associative unital algebra over a commutative ring, the fixed-sign bracket is

```text
[A,B]_ζ = A B - ζ B A.
```

Concrete endomorphism APIs may specialize this algebra without owning a second copy of the
exchange identities. Finite-product peeling repeatedly moves one fixed element through an
ordered product using these exchange relations, without operator or thermal assumptions.
-/

namespace ScalarExchange

variable {R : Type*} [CommRing R]

open scoped BigOperators

/-- The fixed-sign bracket `[A,B]_ζ = A B - ζ B A` in an associative algebra over a commutative ring. -/
noncomputable def zetaCommutator {A : Type*} [Ring A] [Algebra R A]
    (ζ : R) (a b : A) : A :=
  a * b - ζ • (b * a)

/-- Evaluation of the generic fixed-sign bracket on R-linear endomorphisms. -/
@[simp]
theorem zetaCommutator_apply {V : Type*} [AddCommGroup V] [Module R V]
    (ζ : R) (A B : V →ₗ[R] V) (v : V) :
    zetaCommutator ζ A B v = A (B v) - ζ • B (A v) := by
  simp [zetaCommutator, Module.End.mul_eq_comp]

/-- Additivity in the left argument. -/
theorem zetaCommutator_add_left {A : Type*} [Ring A] [Algebra R A]
    (ζ : R) (a b c : A) :
    zetaCommutator ζ (a + b) c =
      zetaCommutator ζ a c + zetaCommutator ζ b c := by
  simp only [zetaCommutator, add_mul, mul_add, smul_add]
  module

/-- Additivity in the right argument. -/
theorem zetaCommutator_add_right {A : Type*} [Ring A] [Algebra R A]
    (ζ : R) (a b c : A) :
    zetaCommutator ζ a (b + c) =
      zetaCommutator ζ a b + zetaCommutator ζ a c := by
  simp only [zetaCommutator, add_mul, mul_add, smul_add]
  module

/-- Scalar multiples factor out of both arguments. -/
theorem zetaCommutator_smul_smul {A : Type*} [Ring A] [Algebra R A]
    (ζ c d : R) (a b : A) :
    zetaCommutator ζ (c • a) (d • b) = (c * d) • zetaCommutator ζ a b := by
  simp only [zetaCommutator, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
  module

/-- Finite sums expand bilinearly in both arguments of the fixed-sign bracket. -/
theorem zetaCommutator_sum_sum {A ι κ : Type*} [Ring A] [Algebra R A]
    (ζ : R) (s : Finset ι) (t : Finset κ) (a : ι → A) (b : κ → A) :
    zetaCommutator ζ (∑ i ∈ s, a i) (∑ j ∈ t, b j) =
      ∑ i ∈ s, ∑ j ∈ t, zetaCommutator ζ (a i) (b j) := by
  have hs : (∑ j ∈ t, ∑ i ∈ s, a i * b j) = ∑ i ∈ s, ∑ j ∈ t, a i * b j :=
    Finset.sum_comm
  simp only [zetaCommutator, Finset.sum_mul, Finset.mul_sum]
  rw [hs]
  simp only [Finset.sum_sub_distrib, Finset.smul_sum]

/-- Reorder a product from a supplied fixed-sign bracket value. -/
theorem mul_eq_add_smul_mul_of_zetaCommutator_eq
    {A : Type*} [Ring A] [Algebra R A] (ζ : R) {a b c : A}
    (h : zetaCommutator ζ a b = c) :
    a * b = c + ζ • (b * a) := by
  have h' : a * b - ζ • (b * a) = c := by
    simpa [zetaCommutator] using h
  exact (sub_eq_iff_eq_add).mp h'

/-- Reversal for an involutive exchange scalar. -/
theorem zetaCommutator_swap_of_sq_eq_one
    {A : Type*} [Ring A] [Algebra R A]
    (ζ : R) (hζ : ζ * ζ = 1) (a b : A) :
    zetaCommutator ζ b a = (-ζ) • zetaCommutator ζ a b := by
  have hneg : (-ζ) * ζ = -1 := by
    calc
      (-ζ) * ζ = -(ζ * ζ) := by ring
      _ = -1 := by rw [hζ]
  simp only [zetaCommutator, smul_sub, smul_smul]
  rw [hneg, neg_one_smul]
  module

/-- The self bracket is `(1 - ζ) A²`. -/
theorem zetaCommutator_self {A : Type*} [Ring A] [Algebra R A]
    (ζ : R) (a : A) :
    zetaCommutator ζ a a = (1 - ζ) • (a * a) := by
  simp [zetaCommutator, sub_smul]

/-- Mixed-sign product rule in the right argument. -/
theorem zetaCommutator_mul_right
    {A : Type*} [Ring A] [Algebra R A]
    (ζ η : R) (a b c : A) :
    zetaCommutator (ζ * η) a (b * c) =
      zetaCommutator ζ a b * c + ζ • (b * zetaCommutator η a c) := by
  simp only [zetaCommutator, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_sub, smul_smul]
  simp only [mul_assoc]
  module

/-- Mixed-sign product rule in the left argument. -/
theorem zetaCommutator_mul_left
    {A : Type*} [Ring A] [Algebra R A]
    (ζ η : R) (a b c : A) :
    zetaCommutator (ζ * η) (a * b) c =
      a * zetaCommutator η b c + η • (zetaCommutator ζ a c * b) := by
  simp only [zetaCommutator, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
    smul_sub, smul_smul]
  simp only [mul_assoc]
  rw [mul_comm ζ η]
  module

/-- Extract commuting scalar factors from an ordered list product of linear endomorphisms,
without changing the order of the endomorphisms. -/
theorem list_prod_map_smul {ι V : Type*} [AddCommGroup V] [Module R V]
    (l : List ι) (a : ι → R) (f : ι → Module.End R V) :
    (l.map (fun i => a i • f i)).prod = (l.map a).prod • (l.map f).prod := by
  induction l with
  | nil => simp
  | cons e l ih =>
      simp only [List.map_cons, List.prod_cons, ih, Module.End.mul_eq_comp,
        LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
      rw [mul_comm (l.map a).prod (a e)]


/-- A weighted finite sum in one distinguished slot of a duplicate-free ordered
product can be expanded without commuting any of the other factors. -/
theorem list_prod_map_weighted_sum_at {ι Label A : Type*} [Fintype ι]
    [Semiring A] [Algebra R A] (l : List Label) (a : Label)
    (hm : a ∈ l) (hn : l.Nodup) (w : ι → R)
    (F : Label → A) (f : ι → Label → A)
    (hF : F a = ∑ i, w i • f i a)
    (hother : ∀ i e, e ≠ a → F e = f i e) :
    (l.map F).prod = ∑ i, w i • (l.map (f i)).prod := by
  classical
  induction l with
  | nil => simp at hm
  | cons b l ih =>
      have hN := List.nodup_cons.mp hn
      by_cases hb : b = a
      · subst b
        have ht (i : ι) : (l.map (f i)).prod = (l.map F).prod := by
          apply congrArg List.prod
          apply List.map_congr_left
          intro e he
          exact (hother i e (fun h => hN.1 (h ▸ he))).symm
        simp only [List.map_cons, List.prod_cons, hF, Finset.sum_mul,
          smul_mul_assoc, ht]
      · have hm' : a ∈ l := (List.mem_cons.mp hm).resolve_left (Ne.symm hb)
        simp only [List.map_cons, List.prod_cons, ih hm' hN.2,
          Finset.mul_sum, mul_smul_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [hother i b hb]

end ScalarExchange

/-! ## Finite-product peeling -/

namespace ScalarExchange

/-- Solve the scalar equation left after exchange and rotation: the exchange remainder has
coefficient `s`, and the rotated value has coefficient `q`. No operator or thermal assumptions
enter this field identity. -/
theorem eq_div_mul_of_eq_add_mul_of_eq_mul {F : Type*} [Field F]
    (E P R s q : F) (hExchange : E = P + s * R) (hRotate : E = q * R)
    (hne : q - s ≠ 0) : E = (q / (q - s)) * P := by
  have h : (q - s) * E = q * P := by
    linear_combination q * hExchange - s * hRotate
  calc
    E = (q * P) / (q - s) :=
      (eq_div_iff hne).2 (by simpa only [mul_comm] using h)
    _ = (q / (q - s)) * P := by ring

variable {R : Type*} [CommSemiring R]

/-- The exchange terms generated while pushing one labelled algebra element through a finite tail. -/
noncomputable def peelSum {Label A : Type*} [Semiring A] [Algebra R A]
    (element : Label → A) (exchangeCoeff : Label → Label → R)
    (ζ : R) (C : Label) : List Label → A
  | [] => 0
  | D :: t =>
      exchangeCoeff C D • (t.map element).prod +
        ζ • (element D * peelSum element exchangeCoeff ζ C t)

@[simp]
theorem peelSum_nil {Label A : Type*} [Semiring A] [Algebra R A]
    (element : Label → A) (exchangeCoeff : Label → Label → R)
    (ζ : R) (C : Label) :
    peelSum element exchangeCoeff ζ C [] = 0 := rfl

/-- The recursive exchange sum is a finite sum over the removed position. The remaining factors
retain their original order; no commutativity or exchange relation is required. -/
theorem peelSum_eq_sum {Label A : Type*} [Semiring A] [Algebra R A]
    (element : Label → A) (exchangeCoeff : Label → Label → R)
    (ζ : R) (C : Label) (l : List Label) :
    peelSum element exchangeCoeff ζ C l =
      ∑ j : Fin l.length,
        (ζ ^ (j : ℕ) * exchangeCoeff C (l[(j : ℕ)]'j.isLt)) •
          ((l.eraseIdx j).map element).prod := by
  induction l with
  | nil => simp [peelSum]
  | cons D t ih =>
      rw [peelSum]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, List.getElem_cons_zero,
        List.eraseIdx_cons_zero]
      congr 1
      rw [ih, Finset.mul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.val_succ, List.getElem_cons_succ, List.eraseIdx_cons_succ,
        List.map_cons, List.prod_cons, pow_succ, mul_smul_comm, smul_smul]
      congr 1
      ring

/-- Peel a fixed element through a finite product when the exchange relation holds only
for factors appearing in the given list. No relations between the tail factors are needed. -/
theorem mul_prod_eq_peelSum_of_mem
    {Label A : Type*} [Semiring A] [Algebra R A]
    (element : Label → A) (exchangeCoeff : Label → Label → R) (ζ : R)
    (C : Label) (l : List Label) :
    (∀ D ∈ l,
      element C * element D =
        exchangeCoeff C D • (1 : A) + ζ • (element D * element C)) →
    element C * (l.map element).prod =
      peelSum element exchangeCoeff ζ C l +
        ζ ^ l.length • ((l.map element).prod * element C) := by
  induction l with
  | nil =>
      intro _
      simp [peelSum]
  | cons D t ih =>
      intro hExchange
      have hhead := hExchange D (by simp)
      have htail : ∀ E ∈ t,
          element C * element E =
            exchangeCoeff C E • (1 : A) + ζ • (element E * element C) := by
        intro E hE
        exact hExchange E (List.mem_cons_of_mem D hE)
      have iht := ih htail
      simp only [List.map_cons, List.prod_cons, peelSum, List.length_cons]
      rw [← mul_assoc, hhead, add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
      rw [mul_assoc (element D) (element C) _, iht, mul_add, mul_smul_comm]
      rw [smul_add, smul_smul, pow_succ, ← mul_assoc]
      module

/-- Repeatedly apply a globally valid scalar exchange relation while pushing one algebra
element through a finite ordered product. This is the global-hypothesis specialization of
`mul_prod_eq_peelSum_of_mem`. -/
theorem mul_prod_eq_peelSum
    {Label A : Type*} [Semiring A] [Algebra R A]
    (element : Label → A) (exchangeCoeff : Label → Label → R) (ζ : R)
    (hExchange : ∀ C D,
      element C * element D =
        exchangeCoeff C D • (1 : A) + ζ • (element D * element C))
    (C : Label) (l : List Label) :
    element C * (l.map element).prod =
      peelSum element exchangeCoeff ζ C l +
        ζ ^ l.length • ((l.map element).prod * element C) :=
  mul_prod_eq_peelSum_of_mem element exchangeCoeff ζ C l
    (fun D _ => hExchange C D)

/-- The coefficient-paired view of the generic exchange sum. Both APIs use the same
recursion, so their finite-position expansions cannot diverge. -/
noncomputable def peelSumWithCoefficients {A : Type*} [Semiring A] [Algebra R A]
    (ζ : R) : List (A × R) → A :=
  peelSum Prod.fst (fun _ p => p.2) ζ (0, 0)

@[simp]
theorem peelSumWithCoefficients_nil {A : Type*} [Semiring A] [Algebra R A]
    (ζ : R) : peelSumWithCoefficients (A := A) ζ [] = 0 := rfl

/-- Computation on a nonempty coefficient-paired list, derived from the canonical peel recursion. -/
@[simp]
theorem peelSumWithCoefficients_cons {A : Type*} [Semiring A] [Algebra R A]
    (ζ : R) (B : A) (c : R) (t : List (A × R)) :
    peelSumWithCoefficients ζ ((B, c) :: t) =
      c • (t.map Prod.fst).prod + ζ • (B * peelSumWithCoefficients ζ t) := rfl

/-- Both peel sums encode the same recursion; the first label is only used to select
its coefficients, which the paired representation already stores in each list element. -/
private theorem peelSumWithCoefficients_eq_peelSum {A : Type*} [Semiring A] [Algebra R A]
    (ζ : R) (C : A) (l : List (A × R)) :
    peelSumWithCoefficients ζ l =
      peelSum Prod.fst (fun _ p => p.2) ζ (C, 0) l := by
  unfold peelSumWithCoefficients
  induction l with
  | nil => rfl
  | cons p t ih =>
      obtain ⟨B, c⟩ := p
      simpa only [peelSumWithCoefficients, peelSum, ih]

/-- Position-indexed expansion when each factor carries its exchange coefficient. -/
theorem peelSumWithCoefficients_eq_sum {A : Type*} [Semiring A] [Algebra R A]
    (ζ : R) (l : List (A × R)) :
    peelSumWithCoefficients ζ l =
      ∑ j : Fin l.length,
        (ζ ^ (j : ℕ) * (l[(j : ℕ)]'j.isLt).2) •
          ((l.eraseIdx j).map Prod.fst).prod := by
  rw [peelSumWithCoefficients_eq_peelSum ζ (0 : A) l, peelSum_eq_sum]

/-- Repeatedly apply a scalar exchange relation between one fixed element and the factors of a
coefficient-paired list. This form is useful when the exchange coefficients depend on the fixed
element, so no relations between the factors themselves are required. -/
theorem mul_prod_eq_peelSumWithCoefficients
    {A : Type*} [Semiring A] [Algebra R A]
    (ζ : R) (C : A) (l : List (A × R))
    (hExchange : ∀ p ∈ l,
      C * p.1 = p.2 • (1 : A) + ζ • (p.1 * C)) :
    C * (l.map Prod.fst).prod =
      peelSumWithCoefficients ζ l + ζ ^ l.length • ((l.map Prod.fst).prod * C) := by
  have h := mul_prod_eq_peelSum_of_mem
    Prod.fst (fun _ p => p.2) ζ (C, 0) l
    (fun p hp => hExchange p hp)
  simpa only [← peelSumWithCoefficients_eq_peelSum ζ C l] using h

end ScalarExchange
