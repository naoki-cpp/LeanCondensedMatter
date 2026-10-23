import LeanCondensedMatter.Analysis.ScalarExchange.Peel
import LeanCondensedMatter.Analysis.Operator.TraceClass.Cyclicity
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
Gibbs/KMS rotation with the explicit grand-canonical generator `K = H - μ N̂`, the
first-pair reduction, and the completed fermionic grand-canonical pairing expansion.

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

/-- A complex exponential of a real number has positive real value, so its
sum with one never vanishes. No condition on the sign of the exponent is needed. -/
private theorem one_add_exp_ofReal_ne_zero (x : ℝ) :
    (1 : ℂ) + Complex.exp (x : ℂ) ≠ 0 := by
  have hr : (1 : ℝ) + Real.exp x ≠ 0 :=
    ne_of_gt (add_pos (by norm_num) (Real.exp_pos x))
  have hc : (((1 : ℝ) + Real.exp x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hr
  simpa only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_exp] using hc

omit [LinearOrder Mode] in
/-- The fermionic KMS denominator is nonzero for every ladder, temperature,
chemical potential, and real one-particle energy. -/
theorem one_add_gibbsFactor_ne_zero
    (ε : Mode → ℝ) (β : ℝ) (C : CompletedThermalLadder Mode) :
    (1 : ℂ) + C.gibbsFactor ε β ≠ 0 := by
  cases C with
  | create i =>
      change (1 : ℂ) + Complex.exp (-(β : ℂ) * (ε i : ℂ)) ≠ 0
      convert one_add_exp_ofReal_ne_zero (-β * ε i) using 1 <;> push_cast <;> ring
  | annihilate i =>
      change (1 : ℂ) + Complex.exp ((β : ℂ) * (ε i : ℂ)) ≠ 0
      convert one_add_exp_ofReal_ne_zero (β * ε i) using 1 <;> push_cast <;> ring

/-- Uniform completed free-Gibbs intertwining for a creation or annihilation operator. -/
theorem grandCanonicalGibbsDensityOperator_comp_operator
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (C : CompletedThermalLadder Mode) :
    (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op.comp C.operator =
      C.gibbsFactor (fun i => ε i - μ) β •
        (C.operator.comp
          (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op) := by
  cases C with
  | create i =>
      exact grandCanonicalGibbsDensityOperator_comp_create ε β μ hsum i
  | annihilate i =>
      exact grandCanonicalGibbsDensityOperator_comp_annihilate ε β μ hsum i

/-- Uniform completed CAR: the anticommutator of any two thermal ladder operators is their scalar
coefficient times the identity. -/
theorem completedAnticomm_operator_operator
    (C D : CompletedThermalLadder Mode) :
    ScalarExchange.zetaCommutator (-1 : ℂ) C.operator D.operator =
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
noncomputable def operatorProduct (l : List (CompletedThermalLadder Mode)) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  (l.map operator).prod

@[simp]
theorem operatorProduct_nil :
    operatorProduct ([] : List (CompletedThermalLadder Mode)) =
      ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) := rfl

@[simp]
theorem operatorProduct_cons (C : CompletedThermalLadder Mode)
    (t : List (CompletedThermalLadder Mode)) :
    operatorProduct (C :: t) = C.operator.comp (operatorProduct t) := by
  simp only [operatorProduct, List.map_cons, List.prod_cons, ContinuousLinearMap.mul_def]

/-- Products respect list concatenation. -/
theorem operatorProduct_append (l₁ l₂ : List (CompletedThermalLadder Mode)) :
    operatorProduct (l₁ ++ l₂) = (operatorProduct l₁).comp (operatorProduct l₂) := by
  simp [operatorProduct, List.map_append, List.prod_append, ContinuousLinearMap.mul_def]

private theorem operator_mul_operator_eq_exchange
    (C D : CompletedThermalLadder Mode) :
    C.operator * D.operator =
      C.anticommutatorValue D •
          (1 : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) +
        (-1 : ℂ) • (D.operator * C.operator) := by
  have hone :
      (1 : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) =
        ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) := rfl
  rw [hone]
  exact ScalarExchange.mul_eq_add_smul_mul_of_zetaCommutator_eq
    (-1 : ℂ) (completedAnticomm_operator_operator C D)

private theorem operator_comp_operatorProduct_eq_peelSum
    (C₁ : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    C₁.operator.comp (operatorProduct l) =
      ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C₁ l +
        ((-1 : ℂ) ^ l.length) • ((operatorProduct l).comp C₁.operator) := by
  have h := ScalarExchange.mul_prod_eq_peelSum
    operator anticommutatorValue (-1 : ℂ)
    operator_mul_operator_eq_exchange C₁ l
  simpa [operatorProduct, ContinuousLinearMap.mul_def] using h

/-- Canonical completed free-Gibbs expectation of an ordered thermal-ladder list. -/
noncomputable def grandCanonicalGibbsExpectation
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (l : List (CompletedThermalLadder Mode)) : ℂ :=
  (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).expectation (operatorProduct l)

@[simp]
theorem grandCanonicalGibbsExpectation_nil
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β) :
    grandCanonicalGibbsExpectation ε β μ hsum [] = 1 := by
  simp [grandCanonicalGibbsExpectation]

/-- Expectation-level exchange formula before the KMS rotation of the final term. -/
theorem grandCanonicalGibbsExpectation_cons_eq_peel_add_rotated
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (C₁ : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    grandCanonicalGibbsExpectation ε β μ hsum (C₁ :: l) =
      (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).expectation (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C₁ l) +
        ((-1 : ℂ) ^ l.length) * grandCanonicalGibbsExpectation ε β μ hsum (l ++ [C₁]) := by
  rw [grandCanonicalGibbsExpectation, operatorProduct_cons,
    operator_comp_operatorProduct_eq_peelSum C₁ l]
  rw [map_add, map_smul]
  simp only [smul_eq_mul]
  rw [grandCanonicalGibbsExpectation, operatorProduct_append]
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

/-- Expectation of the completed CAR peel as an indexed finite sum over the removed tail position. -/
private theorem grandCanonicalGibbsExpectation_peelSum_eq_sum
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (C₁ : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).expectation (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C₁ l) =
      ∑ j : Fin l.length,
        ((-1 : ℂ) ^ (j : ℕ)) * C₁.anticommutatorValue (l[(j : ℕ)]'j.isLt) *
          grandCanonicalGibbsExpectation ε β μ hsum (l.eraseIdx j) := by
  rw [ScalarExchange.peelSum_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  simp only [smul_eq_mul, grandCanonicalGibbsExpectation, operatorProduct]

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
theorem grandCanonicalGibbsExpectation_operator_comp
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (C : CompletedThermalLadder Mode)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).expectation (C.operator.comp A) =
      C.gibbsFactor (fun i => ε i - μ) β *
        (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).expectation (A.comp C.operator) := by
  let ρ := Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum
  have hcomm := grandCanonicalGibbsDensityOperator_comp_operator ε β μ hsum C
  change ρ.op * C.operator = C.gibbsFactor (fun i => ε i - μ) β • (C.operator * ρ.op) at hcomm
  rw [DensityOperator.expectation_apply, DensityOperator.expectation_apply]
  calc
    _ = (((ρ.isTraceClass.comp_right A).comp_left C.operator).smul
        (C.gibbsFactor (fun i => ε i - μ) β)).trace := by
      apply ContinuousLinearMap.IsTraceClass.trace_congr
      change ρ.op * (C.operator * A) =
        C.gibbsFactor (fun i => ε i - μ) β • (C.operator * (ρ.op * A))
      rw [← mul_assoc, hcomm, smul_mul_assoc, mul_assoc]
    _ = C.gibbsFactor (fun i => ε i - μ) β * ((ρ.isTraceClass.comp_right A).comp_left C.operator).trace :=
      ((ρ.isTraceClass.comp_right A).comp_left C.operator).trace_smul _
    _ = _ := by
      simpa only [← ContinuousLinearMap.mul_def, mul_assoc] using
        congrArg (fun z : ℂ => C.gibbsFactor (fun i => ε i - μ) β * z)
          ((ρ.isTraceClass.comp_right A).trace_comp_comm C.operator).symm

/-- KMS rotation specialized to an ordered thermal-ladder tail. -/
theorem grandCanonicalGibbsExpectation_cons_eq_gibbsFactor_mul_rotate
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (C : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    grandCanonicalGibbsExpectation ε β μ hsum (C :: l) =
      C.gibbsFactor (fun i => ε i - μ) β * grandCanonicalGibbsExpectation ε β μ hsum (l ++ [C]) := by
  rw [grandCanonicalGibbsExpectation, operatorProduct_cons,
    grandCanonicalGibbsExpectation_operator_comp ε β μ hsum C]
  rw [grandCanonicalGibbsExpectation, operatorProduct_append]
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

/-- For an odd tail, completed CAR exchange followed by KMS rotation solves the wrapped term.
The coefficient `g / (1 + g)` is the Fermi thermal factor attached to the leading ladder. -/
theorem grandCanonicalGibbsExpectation_cons_eq_gibbsRatio_mul_peel
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (n : ℕ) (C : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode))
    (hlen : l.length = 2 * n + 1) :
    grandCanonicalGibbsExpectation ε β μ hsum (C :: l) =
      (C.gibbsFactor (fun i => ε i - μ) β / ((1 : ℂ) + C.gibbsFactor (fun i => ε i - μ) β)) *
        (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).expectation (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C l) := by
  set E : ℂ := grandCanonicalGibbsExpectation ε β μ hsum (C :: l)
  set P : ℂ :=
    (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).expectation (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C l)
  set R : ℂ := grandCanonicalGibbsExpectation ε β μ hsum (l ++ [C])
  have hpeel : E = P + ((-1 : ℂ) ^ l.length) * R := by
    simpa [E, P, R] using
      grandCanonicalGibbsExpectation_cons_eq_peel_add_rotated ε β μ hsum C l
  have hkms : E = C.gibbsFactor (fun i => ε i - μ) β * R := by
    simpa [E, R] using
      grandCanonicalGibbsExpectation_cons_eq_gibbsFactor_mul_rotate ε β μ hsum C l
  have hsign : ((-1 : ℂ) ^ l.length) = -1 := by
    rw [hlen]
    have hmod : (2 * n + 1) % 2 = 1 % 2 := by omega
    have h := Common.BlochDeDominicis.zetaInt_pow_eq_of_mod_two_eq
      Common.Statistics.fermion hmod
    simpa using h
  simpa only [sub_neg_eq_add, add_comm] using
    ScalarExchange.eq_div_mul_of_eq_add_mul_of_eq_mul E P R (-1) (C.gibbsFactor (fun i => ε i - μ) β)
      (by simpa only [hsign] using hpeel) hkms
      (by simpa only [sub_neg_eq_add, add_comm] using
        (one_add_gibbsFactor_ne_zero (fun i => ε i - μ) β C))

/-- The normalized two-point completed Gibbs expectation is the scalar CAR coefficient multiplied
by the same Gibbs ratio that solves the odd-tail KMS equation. -/
theorem grandCanonicalGibbsExpectation_pair_eq
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (C D : CompletedThermalLadder Mode) :
    grandCanonicalGibbsExpectation ε β μ hsum [C, D] =
      (C.gibbsFactor (fun i => ε i - μ) β / ((1 : ℂ) + C.gibbsFactor (fun i => ε i - μ) β)) *
        C.anticommutatorValue D := by
  have h := grandCanonicalGibbsExpectation_cons_eq_gibbsRatio_mul_peel
    ε β μ hsum 0 C [D] (by simp)
  have hpeel :
      (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).expectation
          (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) C [D]) =
        C.anticommutatorValue D := by
    have hone :
        (1 : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) =
          ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) := rfl
    simp [ScalarExchange.peelSum, hone]
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
noncomputable def grandCanonicalGibbsExpectationRecursion
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β) :
    Common.BlochDeDominicis.ExpectationPairingRecursion
      (CompletedThermalLadder Mode) Common.Statistics.fermion where
  expectation := grandCanonicalGibbsExpectation ε β μ hsum
  pairValue := fun C D => grandCanonicalGibbsExpectation ε β μ hsum [C, D]
  admissible := fun _ _ => True
  expectation_nil := grandCanonicalGibbsExpectation_nil ε β μ hsum
  admissible_erase := fun _ _ _ _ => trivial
  expectation_succ := by
    intro n C _
    rw [List.ofFn_succ]
    set l : List (CompletedThermalLadder Mode) :=
      List.ofFn (fun i : Fin (2 * n + 1) => C i.succ) with hl
    have hlen : l.length = 2 * n + 1 := by
      rw [hl]
      simp
    calc
      grandCanonicalGibbsExpectation ε β μ hsum (C 0 :: l) =
        ((C 0).gibbsFactor (fun i => ε i - μ) β / ((1 : ℂ) + (C 0).gibbsFactor (fun i => ε i - μ) β)) *
          (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).expectation
            (ScalarExchange.peelSum operator anticommutatorValue (-1 : ℂ) (C 0) l) :=
        grandCanonicalGibbsExpectation_cons_eq_gibbsRatio_mul_peel
          ε β μ hsum n (C 0) l hlen
      _ = ∑ j : Fin (2 * n + 1),
          (Common.Statistics.fermion.zetaInt : ℂ) ^ (j : ℕ) *
            grandCanonicalGibbsExpectation ε β μ hsum [C 0, C j.succ] *
              grandCanonicalGibbsExpectation ε β μ hsum
                (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ)) := by
        rw [grandCanonicalGibbsExpectation_peelSum_eq_sum, Finset.mul_sum]
        rw [hl, List.sum_getElem_eraseIdx_ofFn
          (fun i : Fin (2 * n + 1) => C i.succ)
          (fun i field rest =>
            ((C 0).gibbsFactor (fun i => ε i - μ) β / ((1 : ℂ) + (C 0).gibbsFactor (fun i => ε i - μ) β)) *
              (((-1 : ℂ) ^ i) * (C 0).anticommutatorValue field *
                grandCanonicalGibbsExpectation ε β μ hsum rest))]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hpair := grandCanonicalGibbsExpectation_pair_eq
          ε β μ hsum (C 0) (C j.succ)
        rw [hpair]
        simp only [Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one]
        ring

/-- Completed free-fermion Bloch--de Dominicis expansion obtained by feeding the completed Gibbs
recursion data into the common pairing induction. -/
theorem grandCanonicalGibbsExpectation_eq_sum_pairing
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (n : ℕ) (C : Fin (2 * n) → CompletedThermalLadder Mode) :
    grandCanonicalGibbsExpectation ε β μ hsum (List.ofFn C) =
      ∑ pairing : Pairing n,
        pairing.weight Common.Statistics.fermion *
          ∏ pr ∈ pairing.pairs,
            grandCanonicalGibbsExpectation ε β μ hsum [C pr.1, C pr.2] := by
  simpa [grandCanonicalGibbsExpectationRecursion] using
    (Common.BlochDeDominicis.ExpectationPairingRecursion.bloch_de_dominicis
      (grandCanonicalGibbsExpectationRecursion ε β μ hsum) n C trivial)

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization
