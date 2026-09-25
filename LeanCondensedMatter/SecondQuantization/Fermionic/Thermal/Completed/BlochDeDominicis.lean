import LeanCondensedMatter.Analysis.ScalarExchange
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.Gibbs
import Mathlib.Tactic.Module
import LeanCondensedMatter.Combinatorics.FiniteIndex.EraseIdxOfFn
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion

set_option linter.style.header false

/-!
# Completed free-fermion Bloch--de Dominicis theorem

This module contains the representation-specific data needed to instantiate the generic
`Common.BlochDeDominicis.ExpectationPairingRecursion`: bounded ladder packaging, CAR peeling,
Gibbs/KMS rotation, the first-pair reduction, and the final completed free-Gibbs pairing expansion.

These declarations form one proof pipeline rather than independent public subsystems, so they are
kept together while the statistics-independent pairing induction remains in `Common.Thermal`.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

/-- A single bounded fermionic ladder operator in the completed representation. -/
inductive CompletedThermalLadder (Mode : Type*) where
  | create (i : Mode)
  | annihilate (i : Mode)
  deriving DecidableEq

namespace CompletedThermalLadder

/-- The bounded completed-Fock-space operator represented by a thermal ladder label. -/
noncomputable def operator : CompletedThermalLadder Mode →
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode
  | .create i => completedCreate i
  | .annihilate i => completedAnnihilate i

/-- The one-mode scalar appearing when the Gibbs density operator is commuted past a ladder
operator. -/
noncomputable def gibbsFactor (ε : Mode → ℝ) (β : ℝ) : CompletedThermalLadder Mode → ℂ
  | .create i => Complex.exp (-(β : ℂ) * (ε i : ℂ))
  | .annihilate i => Complex.exp ((β : ℂ) * (ε i : ℂ))

/-- The scalar anticommutator coefficient for two completed fermionic ladder operators. -/
noncomputable def anticommutatorValue :
    CompletedThermalLadder Mode → CompletedThermalLadder Mode → ℂ
  | .create _, .create _ => 0
  | .annihilate _, .annihilate _ => 0
  | .create i, .annihilate j => if i = j then 1 else 0
  | .annihilate i, .create j => if i = j then 1 else 0

@[simp]
theorem operator_create (i : Mode) :
    operator (CompletedThermalLadder.create i) = completedCreate i := rfl

@[simp]
theorem operator_annihilate (i : Mode) :
    operator (CompletedThermalLadder.annihilate i) = completedAnnihilate i := rfl

omit [LinearOrder Mode] in
@[simp]
theorem gibbsFactor_create (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    gibbsFactor ε β (CompletedThermalLadder.create i) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) := rfl

omit [LinearOrder Mode] in
@[simp]
theorem gibbsFactor_annihilate (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    gibbsFactor ε β (CompletedThermalLadder.annihilate i) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) := rfl

/-- Uniform completed free-Gibbs intertwining for a creation or annihilation operator. -/
theorem completedFreeGibbsDensityOperator_comp_operator
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (C : CompletedThermalLadder Mode) :
    (completedFreeGibbsDensityOperator ε β hsum).op.comp C.operator =
      C.gibbsFactor ε β •
        (C.operator.comp
          (completedFreeGibbsDensityOperator ε β hsum).op) := by
  cases C with
  | create i =>
      exact completedFreeGibbsDensityOperator_comp_create ε β hsum i
  | annihilate i =>
      exact completedFreeGibbsDensityOperator_comp_annihilate ε β hsum i

/-- Uniform completed CAR: the anticommutator of any two thermal ladder operators is their scalar
coefficient times the identity. -/
theorem completedAnticomm_operator_operator
    (C D : CompletedThermalLadder Mode) :
    completedAnticomm C.operator D.operator =
      C.anticommutatorValue D •
        ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) := by
  cases C with
  | create i =>
      cases D with
      | create j =>
          rw [operator_create, operator_create, completedAnticomm_create_create]
          simp [anticommutatorValue]
      | annihilate j =>
          rw [operator_create, operator_annihilate, completedAnticomm_create_annihilate]
          by_cases h : i = j <;> simp [anticommutatorValue, h]
  | annihilate i =>
      cases D with
      | create j =>
          rw [operator_annihilate, operator_create, completedAnticomm_annihilate_create]
          by_cases h : i = j <;> simp [anticommutatorValue, h]
      | annihilate j =>
          rw [operator_annihilate, operator_annihilate, completedAnticomm_annihilate_annihilate]
          simp [anticommutatorValue]

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

namespace CompletedThermalLadder

/-- Right-associated bounded product of completed thermal ladder operators. -/
noncomputable def operatorProduct : List (CompletedThermalLadder Mode) →
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode
  | [] => ContinuousLinearMap.id ℂ (CompletedFockSpace Mode)
  | C :: t => C.operator.comp (operatorProduct t)

@[simp]
theorem operatorProduct_nil :
    operatorProduct ([] : List (CompletedThermalLadder Mode)) =
      ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) := rfl

@[simp]
theorem operatorProduct_cons (C : CompletedThermalLadder Mode)
    (t : List (CompletedThermalLadder Mode)) :
    operatorProduct (C :: t) = C.operator.comp (operatorProduct t) := rfl

/-- Products respect list concatenation. -/
theorem operatorProduct_append (l₁ l₂ : List (CompletedThermalLadder Mode)) :
    operatorProduct (l₁ ++ l₂) = (operatorProduct l₁).comp (operatorProduct l₂) := by
  induction l₁ with
  | nil => simp
  | cons C t ih =>
      rw [List.cons_append, operatorProduct_cons, operatorProduct_cons, ih,
        ContinuousLinearMap.comp_assoc]

private theorem operatorProduct_eq_prod
    (l : List (CompletedThermalLadder Mode)) :
    operatorProduct l = (l.map operator).prod := by
  induction l with
  | nil => rfl
  | cons C t ih =>
      rw [operatorProduct_cons, List.map_cons, List.prod_cons, ih]
      rfl

private theorem operator_mul_operator_eq_exchange
    (C D : CompletedThermalLadder Mode) :
    C.operator * D.operator =
      C.anticommutatorValue D •
          (1 : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) +
        (-1 : ℂ) • (D.operator * C.operator) := by
  apply ContinuousLinearMap.ext
  intro ψ
  have hcar := DFunLike.congr_fun (completedAnticomm_operator_operator C D) ψ
  simp only [completedAnticomm_apply, smul_apply, ContinuousLinearMap.id_apply] at hcar
  change C.operator (D.operator ψ) =
    C.anticommutatorValue D • ψ + (-1 : ℂ) • D.operator (C.operator ψ)
  simpa [sub_eq_add_neg] using (eq_sub_of_add_eq hcar)

private theorem operator_comp_operatorProduct_eq_peelSum
    (C₁ : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    C₁.operator.comp (operatorProduct l) =
      ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C₁ l +
        ((-1 : ℂ) ^ l.length) • ((operatorProduct l).comp C₁.operator) := by
  have h := ScalarExchange.mul_prod_eq_peelSum
    operator anticommutatorValue (-1 : ℂ)
    operator_mul_operator_eq_exchange C₁ l
  rw [← operatorProduct_eq_prod l] at h
  simpa [ContinuousLinearMap.mul_def] using h

/-- Canonical completed free-Gibbs expectation of an ordered thermal-ladder list. -/
noncomputable def completedFreeGibbsExpectation
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (l : List (CompletedThermalLadder Mode)) : ℂ :=
  (completedFreeGibbsDensityOperator ε β hsum).expectation (operatorProduct l)

@[simp]
theorem completedFreeGibbsExpectation_nil
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β) :
    completedFreeGibbsExpectation ε β hsum [] = 1 := by
  simp [completedFreeGibbsExpectation]

/-- Expectation-level exchange formula before the KMS rotation of the final term. -/
theorem completedFreeGibbsExpectation_cons_eq_peel_add_rotated
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (C₁ : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    completedFreeGibbsExpectation ε β hsum (C₁ :: l) =
      (completedFreeGibbsDensityOperator ε β hsum).expectation (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C₁ l) +
        ((-1 : ℂ) ^ l.length) * completedFreeGibbsExpectation ε β hsum (l ++ [C₁]) := by
  rw [completedFreeGibbsExpectation, operatorProduct_cons,
    operator_comp_operatorProduct_eq_peelSum C₁ l]
  rw [map_add, map_smul]
  simp only [smul_eq_mul]
  rw [completedFreeGibbsExpectation, operatorProduct_append]
  simp

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

namespace CompletedThermalLadder

/-- Individual completed CAR peel terms, one for each operator in the tail. -/
private noncomputable def thermalPeelTerms (C₁ : CompletedThermalLadder Mode) :
    List (CompletedThermalLadder Mode) →
      List (CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode)
  | [] => []
  | D :: t =>
      (C₁.anticommutatorValue D • operatorProduct t) ::
        (thermalPeelTerms C₁ t).map (fun A => (-1 : ℂ) • (D.operator.comp A))

/-- The recursive completed peel sum is the sum of its individual terms. -/
private theorem peelSum_eq_thermalPeelTerms_sum
    (C₁ : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C₁ l = (thermalPeelTerms C₁ l).sum := by
  induction l with
  | nil => simp [ScalarExchange.peelSum, thermalPeelTerms]
  | cons D t ih =>
      have hmap : ∀ L : List (CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode),
          (L.map (fun A => (-1 : ℂ) • (D.operator.comp A))).sum =
            (-1 : ℂ) • (D.operator.comp L.sum) := by
        intro L
        induction L with
        | nil => simp
        | cons A T ihT =>
            rw [List.map_cons, List.sum_cons, List.sum_cons, ihT]
            apply ContinuousLinearMap.ext
            intro ψ
            simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, map_add]
            module
      rw [ScalarExchange.peelSum, thermalPeelTerms, List.sum_cons, hmap, ← ih,
        ← operatorProduct_eq_prod t, ContinuousLinearMap.mul_def]

/-- Closed position-indexed form of the completed CAR peel terms. -/
private theorem thermalPeelTerms_eq_ofFn
    (C₁ : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    thermalPeelTerms C₁ l =
      List.ofFn (fun j : Fin l.length =>
        (((-1 : ℂ) ^ (j : ℕ)) * C₁.anticommutatorValue (l[(j : ℕ)]'j.isLt)) •
          operatorProduct (l.eraseIdx j)) := by
  induction l with
  | nil => simp [thermalPeelTerms]
  | cons D t ih =>
      rw [List.ofFn_succ, thermalPeelTerms]
      simp only [Fin.val_zero, pow_zero, one_mul, List.getElem_cons_zero,
        List.eraseIdx_cons_zero]
      congr 1
      rw [ih, List.map_ofFn]
      congr 1
      funext i
      change (-1 : ℂ) •
          (D.operator.comp
            ((((-1 : ℂ) ^ (i : ℕ)) *
                C₁.anticommutatorValue (t[(i : ℕ)]'i.isLt)) •
              operatorProduct (t.eraseIdx i))) =
        (((-1 : ℂ) ^ ((i.succ : Fin (t.length + 1)) : ℕ)) *
            C₁.anticommutatorValue
              (((D :: t))[((i.succ : Fin (t.length + 1)) : ℕ)]'
                (i.succ : Fin (t.length + 1)).isLt)) •
          operatorProduct ((D :: t).eraseIdx (i.succ : Fin (t.length + 1)))
      simp only [Fin.val_succ, List.getElem_cons_succ, List.eraseIdx_cons_succ,
        operatorProduct_cons, pow_succ]
      apply ContinuousLinearMap.ext
      intro ψ
      simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul]
      module

/-- Expectation of the completed CAR peel as an indexed finite sum over the removed tail position. -/
private theorem completedFreeGibbsExpectation_peelSum_eq_sum
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (C₁ : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    (completedFreeGibbsDensityOperator ε β hsum).expectation (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C₁ l) =
      ∑ j : Fin l.length,
        ((-1 : ℂ) ^ (j : ℕ)) * C₁.anticommutatorValue (l[(j : ℕ)]'j.isLt) *
          completedFreeGibbsExpectation ε β hsum (l.eraseIdx j) := by
  have hmap : ∀ L : List (CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode),
      (completedFreeGibbsDensityOperator ε β hsum).expectation L.sum =
        (L.map (completedFreeGibbsDensityOperator ε β hsum).expectation).sum := by
    intro L
    exact map_list_sum
      (completedFreeGibbsDensityOperator ε β hsum).expectation L
  rw [peelSum_eq_thermalPeelTerms_sum, thermalPeelTerms_eq_ofFn, hmap,
    List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp]
  rw [map_smul]
  simp only [smul_eq_mul, completedFreeGibbsExpectation]

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

namespace CompletedThermalLadder

/-- Completed free-Gibbs KMS rotation for one thermal ladder and an arbitrary bounded operator:
`⟨C A⟩β = gβ(C) ⟨A C⟩β`.  The scalar `gβ(C)` is the same factor appearing in
`ρβ C = gβ(C) C ρβ`. -/
theorem completedFreeGibbsExpectation_operator_comp
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (C : CompletedThermalLadder Mode)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    (completedFreeGibbsDensityOperator ε β hsum).expectation (C.operator.comp A) =
      C.gibbsFactor ε β *
        (completedFreeGibbsDensityOperator ε β hsum).expectation (A.comp C.operator) := by
  rw [completedFreeGibbsDensityOperator_expectation_eq_tsum,
    completedFreeGibbsDensityOperator_expectation_eq_tsum, ← tsum_mul_left]
  cases C with
  | create i =>
      simp only [operator_create, gibbsFactor_create]
      let f : Occupation Mode → ℂ := fun n =>
        Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
          ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
            inner ℂ (completedBasisState n)
              ((A.comp (completedCreate i)) (completedBasisState n)))
      calc
        (∑' n : Occupation Mode,
            (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
              inner ℂ (completedBasisState n)
                (((completedCreate i).comp A) (completedBasisState n))) =
            ∑' n : Occupation Mode, f (toggleOccupation i n) := by
          apply tsum_congr
          intro n
          by_cases hi : i ∈ n
          · have hremove : i ∉ removeOccupation i n := by
              simp [removeOccupation]
            have hrestore : insertOccupation i (removeOccupation i n) = n := by
              simpa [insertOccupation, removeOccupation] using Finset.insert_erase hi
            dsimp [f]
            rw [inner_completedBasisState_left, completedCreate_apply, if_pos hi,
              toggleOccupation_of_mem hi,
              coe_completedFreeGibbsProbability_removeOccupation_of_mem ε β hi,
              completedCreate_basisState_of_not_mem hremove, map_smul, inner_smul_right,
              inner_completedBasisState_left, hrestore]
            have hexp :
                Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
                    Complex.exp ((β : ℂ) * (ε i : ℂ)) = 1 := by
              rw [← Complex.exp_add]
              ring_nf
              exact Complex.exp_zero
            calc
              _ = 1 * ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
                  (fermionPhase i (removeOccupation i n) *
                    (A (completedBasisState n)) (removeOccupation i n))) := by ring
              _ = (Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
                    Complex.exp ((β : ℂ) * (ε i : ℂ))) *
                    ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
                      (fermionPhase i (removeOccupation i n) *
                        (A (completedBasisState n)) (removeOccupation i n))) := by
                    rw [hexp]
              _ = _ := by ring
          · have hit : i ∈ toggleOccupation i n :=
              (mem_toggleOccupation i n).mpr hi
            dsimp [f]
            rw [inner_completedBasisState_left, completedCreate_apply, if_neg hi,
              completedCreate_basisState_of_mem hit, map_zero, inner_zero_right]
            ring
        _ = ∑' n : Occupation Mode, f n := by
          simpa [toggleOccupationEquiv_apply] using
            (Equiv.tsum_eq (toggleOccupationEquiv i) f)
        _ = ∑' n : Occupation Mode,
            Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
              ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
                inner ℂ (completedBasisState n)
                  ((A.comp (completedCreate i)) (completedBasisState n))) := by
          rfl
  | annihilate i =>
      simp only [operator_annihilate, gibbsFactor_annihilate]
      let f : Occupation Mode → ℂ := fun n =>
        Complex.exp ((β : ℂ) * (ε i : ℂ)) *
          ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
            inner ℂ (completedBasisState n)
              ((A.comp (completedAnnihilate i)) (completedBasisState n)))
      calc
        (∑' n : Occupation Mode,
            (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
              inner ℂ (completedBasisState n)
                (((completedAnnihilate i).comp A) (completedBasisState n))) =
            ∑' n : Occupation Mode, f (toggleOccupation i n) := by
          apply tsum_congr
          intro n
          by_cases hi : i ∈ n
          · have hit : i ∉ toggleOccupation i n := by
              intro hit
              exact ((mem_toggleOccupation i n).mp hit) hi
            dsimp [f]
            rw [inner_completedBasisState_left, completedAnnihilate_apply, if_pos hi,
              completedAnnihilate_basisState_of_not_mem hit, map_zero, inner_zero_right]
            ring
          · have hinsert : i ∈ insertOccupation i n := by
              simp [insertOccupation]
            have hrestore : removeOccupation i (insertOccupation i n) = n := by
              simp [removeOccupation, insertOccupation, hi]
            dsimp [f]
            rw [inner_completedBasisState_left, completedAnnihilate_apply, if_neg hi,
              toggleOccupation_of_not_mem hi,
              coe_completedFreeGibbsProbability_insertOccupation_of_not_mem ε β hi,
              completedAnnihilate_basisState_of_mem hinsert, map_smul, inner_smul_right,
              inner_completedBasisState_left, hrestore]
            have hexp :
                Complex.exp ((β : ℂ) * (ε i : ℂ)) *
                    Complex.exp (-(β : ℂ) * (ε i : ℂ)) = 1 := by
              rw [← Complex.exp_add]
              ring_nf
              exact Complex.exp_zero
            calc
              _ = 1 * ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
                  (fermionPhase i (insertOccupation i n) *
                    (A (completedBasisState n)) (insertOccupation i n))) := by ring
              _ = (Complex.exp ((β : ℂ) * (ε i : ℂ)) *
                    Complex.exp (-(β : ℂ) * (ε i : ℂ))) *
                    ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
                      (fermionPhase i (insertOccupation i n) *
                        (A (completedBasisState n)) (insertOccupation i n))) := by
                    rw [hexp]
              _ = _ := by ring
        _ = ∑' n : Occupation Mode, f n := by
          simpa [toggleOccupationEquiv_apply] using
            (Equiv.tsum_eq (toggleOccupationEquiv i) f)
        _ = ∑' n : Occupation Mode,
            Complex.exp ((β : ℂ) * (ε i : ℂ)) *
              ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
                inner ℂ (completedBasisState n)
                  ((A.comp (completedAnnihilate i)) (completedBasisState n))) := by
          rfl

/-- KMS rotation specialized to an ordered thermal-ladder tail. -/
theorem completedFreeGibbsExpectation_cons_eq_gibbsFactor_mul_rotate
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (C : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    completedFreeGibbsExpectation ε β hsum (C :: l) =
      C.gibbsFactor ε β * completedFreeGibbsExpectation ε β hsum (l ++ [C]) := by
  rw [completedFreeGibbsExpectation, operatorProduct_cons,
    completedFreeGibbsExpectation_operator_comp ε β hsum C]
  rw [completedFreeGibbsExpectation, operatorProduct_append]
  simp

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

namespace CompletedThermalLadder

/-- Completed free-Gibbs admissibility for an even ladder family.  At this stage the only local
condition needed to solve the fermionic KMS peel equation is the nonvanishing denominator
`1 + gβ(Cᵢ)`. -/
def completedFreeGibbsAdmissible (ε : Mode → ℝ) (β : ℝ) (n : ℕ)
    (C : Fin (2 * n) → CompletedThermalLadder Mode) : Prop :=
  ∀ i, (1 : ℂ) + (C i).gibbsFactor ε β ≠ 0

omit [LinearOrder Mode] in
/-- Completed Gibbs admissibility is stable under deleting the first ladder and one partner. -/
theorem completedFreeGibbsAdmissible_erase
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ)
    (C : Fin (2 * (n + 1)) → CompletedThermalLadder Mode)
    (hC : completedFreeGibbsAdmissible ε β (n + 1) C)
    (j : Fin (2 * n + 1)) :
    completedFreeGibbsAdmissible ε β n
      (fun i : Fin (2 * n) => C ((j.succAbove i).succ)) := by
  intro i
  exact hC _

/-- For an odd tail, completed CAR exchange followed by KMS rotation solves the wrapped term.
The coefficient `g / (1 + g)` is the Fermi thermal factor attached to the leading ladder. -/
theorem completedFreeGibbsExpectation_cons_eq_gibbsRatio_mul_peel
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (n : ℕ) (C : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode))
    (hlen : l.length = 2 * n + 1)
    (hne : (1 : ℂ) + C.gibbsFactor ε β ≠ 0) :
    completedFreeGibbsExpectation ε β hsum (C :: l) =
      (C.gibbsFactor ε β / ((1 : ℂ) + C.gibbsFactor ε β)) *
        (completedFreeGibbsDensityOperator ε β hsum).expectation (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C l) := by
  set E : ℂ := completedFreeGibbsExpectation ε β hsum (C :: l)
  set P : ℂ :=
    (completedFreeGibbsDensityOperator ε β hsum).expectation (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C l)
  set R : ℂ := completedFreeGibbsExpectation ε β hsum (l ++ [C])
  have hpeel : E = P + ((-1 : ℂ) ^ l.length) * R := by
    simpa [E, P, R] using
      completedFreeGibbsExpectation_cons_eq_peel_add_rotated ε β hsum C l
  have hkms : E = C.gibbsFactor ε β * R := by
    simpa [E, R] using
      completedFreeGibbsExpectation_cons_eq_gibbsFactor_mul_rotate ε β hsum C l
  have hsign : ((-1 : ℂ) ^ l.length) = -1 := by
    rw [hlen]
    have hmod : (2 * n + 1) % 2 = 1 % 2 := by omega
    have h := Common.BlochDeDominicis.zetaInt_pow_eq_of_mod_two_eq
      Common.Statistics.fermion hmod
    simpa using h
  have hgr : C.gibbsFactor ε β * R = P - R := by
    calc
      C.gibbsFactor ε β * R = E := hkms.symm
      _ = P + ((-1 : ℂ) ^ l.length) * R := hpeel
      _ = P - R := by rw [hsign]; ring
  have hRmul : R * ((1 : ℂ) + C.gibbsFactor ε β) = P := by
    calc
      R * ((1 : ℂ) + C.gibbsFactor ε β) = C.gibbsFactor ε β * R + R := by ring
      _ = (P - R) + R := by rw [hgr]
      _ = P := by ring
  have hR : R = P / ((1 : ℂ) + C.gibbsFactor ε β) :=
    (eq_div_iff hne).2 hRmul
  calc
    completedFreeGibbsExpectation ε β hsum (C :: l) = E := rfl
    _ = C.gibbsFactor ε β * R := hkms
    _ = (C.gibbsFactor ε β / ((1 : ℂ) + C.gibbsFactor ε β)) * P := by
      rw [hR]
      ring
    _ = (C.gibbsFactor ε β / ((1 : ℂ) + C.gibbsFactor ε β)) *
        (completedFreeGibbsDensityOperator ε β hsum).expectation (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C l) := rfl

/-- The normalized two-point completed Gibbs expectation is the scalar CAR coefficient multiplied
by the same Gibbs ratio that solves the odd-tail KMS equation. -/
theorem completedFreeGibbsExpectation_pair_eq
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (C D : CompletedThermalLadder Mode)
    (hne : (1 : ℂ) + C.gibbsFactor ε β ≠ 0) :
    completedFreeGibbsExpectation ε β hsum [C, D] =
      (C.gibbsFactor ε β / ((1 : ℂ) + C.gibbsFactor ε β)) *
        C.anticommutatorValue D := by
  have h := completedFreeGibbsExpectation_cons_eq_gibbsRatio_mul_peel
    ε β hsum 0 C [D] (by simp) hne
  have hpeel :
      (completedFreeGibbsDensityOperator ε β hsum).expectation (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C [D]) =
        C.anticommutatorValue D := by
    simp [ScalarExchange.peelSum]
  rw [hpeel] at h
  exact h

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization

namespace SecondQuantization
namespace Fermionic

open QuantumTheory
open Combinatorics

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

namespace CompletedThermalLadder

/-- The completed free-fermion Gibbs expectation as an implementation of the generic
Bloch--de Dominicis pairing-recursion contract. -/
noncomputable def completedFreeGibbsExpectationRecursion
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β) :
    Common.BlochDeDominicis.ExpectationPairingRecursion
      (CompletedThermalLadder Mode) Common.Statistics.fermion where
  expectation := completedFreeGibbsExpectation ε β hsum
  pairValue := fun C D => completedFreeGibbsExpectation ε β hsum [C, D]
  admissible := completedFreeGibbsAdmissible ε β
  expectation_nil := completedFreeGibbsExpectation_nil ε β hsum
  admissible_erase := completedFreeGibbsAdmissible_erase ε β
  expectation_succ := by
    intro n C hC
    rw [List.ofFn_succ]
    set l : List (CompletedThermalLadder Mode) :=
      List.ofFn (fun i : Fin (2 * n + 1) => C i.succ) with hl
    have hlen : l.length = 2 * n + 1 := by
      rw [hl]
      simp
    calc
      completedFreeGibbsExpectation ε β hsum (C 0 :: l) =
        ((C 0).gibbsFactor ε β / ((1 : ℂ) + (C 0).gibbsFactor ε β)) *
          (completedFreeGibbsDensityOperator ε β hsum).expectation
            (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) (C 0) l) :=
        completedFreeGibbsExpectation_cons_eq_gibbsRatio_mul_peel
          ε β hsum n (C 0) l hlen (hC 0)
      _ = ∑ j : Fin (2 * n + 1),
          (Common.Statistics.fermion.zetaInt : ℂ) ^ (j : ℕ) *
            completedFreeGibbsExpectation ε β hsum [C 0, C j.succ] *
              completedFreeGibbsExpectation ε β hsum
                (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ)) := by
        rw [completedFreeGibbsExpectation_peelSum_eq_sum, Finset.mul_sum]
        have hreindex :
            (∑ i : Fin l.length,
              ((C 0).gibbsFactor ε β / ((1 : ℂ) + (C 0).gibbsFactor ε β)) *
                (((-1 : ℂ) ^ (i : ℕ)) * (C 0).anticommutatorValue (l[(i : ℕ)]'i.isLt) *
                  completedFreeGibbsExpectation ε β hsum (l.eraseIdx i))) =
              ∑ j : Fin (2 * n + 1),
                ((C 0).gibbsFactor ε β / ((1 : ℂ) + (C 0).gibbsFactor ε β)) *
                  (((-1 : ℂ) ^ (j : ℕ)) * (C 0).anticommutatorValue (C j.succ) *
                    completedFreeGibbsExpectation ε β hsum (l.eraseIdx j)) := by
          rw [← Equiv.sum_comp (finCongr hlen.symm)]
          apply Finset.sum_congr rfl
          intro j _
          simp only [finCongr_apply, Fin.val_cast, hl, List.getElem_ofFn]
        rw [hreindex]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hl, List.eraseIdx_ofFn_eq_ofFn_succAbove]
        have hpair := completedFreeGibbsExpectation_pair_eq
          ε β hsum (C 0) (C j.succ) (hC 0)
        rw [hpair]
        simp only [Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one]
        ring

/-- Completed free-fermion Bloch--de Dominicis expansion obtained by feeding the completed Gibbs
recursion data into the common pairing induction. -/
theorem completedFreeGibbsExpectation_eq_sum_pairing
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (n : ℕ) (C : Fin (2 * n) → CompletedThermalLadder Mode)
    (hC : completedFreeGibbsAdmissible ε β n C) :
    completedFreeGibbsExpectation ε β hsum (List.ofFn C) =
      ∑ pairing : Pairing n,
        pairing.weight Common.Statistics.fermion *
          ∏ pr ∈ pairing.pairs,
            completedFreeGibbsExpectation ε β hsum [C pr.1, C pr.2] := by
  simpa [completedFreeGibbsExpectationRecursion] using
    (Common.BlochDeDominicis.ExpectationPairingRecursion.bloch_de_dominicis
      (completedFreeGibbsExpectationRecursion ε β hsum) n C hC)

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization
