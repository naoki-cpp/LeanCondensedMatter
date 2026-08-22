import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalLadder
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Completed fermionic thermal peel identity

This file supplies the bounded-operator exchange step needed immediately before the completed
free-Gibbs KMS rotation.  It is representation-specific only through `CompletedThermalLadder` and
its completed CAR data; no occupation-basis combinatorics or pairing induction is introduced here.

For a first ladder `C₁` and a tail `D₁, …, Dₖ`, repeated use of

`C₁ Dⱼ + Dⱼ C₁ = c(C₁,Dⱼ) I`

gives

`C₁ (D₁⋯Dₖ) = peel(C₁; D₁,…,Dₖ) + (-1)^k (D₁⋯Dₖ) C₁`.

Applying the canonical completed Gibbs expectation then isolates the sole remaining analytic step:
identifying the rotated final term by the Gibbs/KMS relation.  The subsequent recurrence bridge can
therefore reuse `Common.BlochDeDominicis.ExpectationPairingRecursion` without duplicating its
combinatorics.
-/

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

/-- The sum of contraction terms generated while pushing `C₁` through a ladder list. -/
noncomputable def thermalPeelSum (C₁ : CompletedThermalLadder Mode) :
    List (CompletedThermalLadder Mode) →
      CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode
  | [] => 0
  | D :: t =>
      C₁.anticommutatorValue D • operatorProduct t -
        D.operator.comp (thermalPeelSum C₁ t)

@[simp]
theorem thermalPeelSum_nil (C₁ : CompletedThermalLadder Mode) :
    thermalPeelSum C₁ [] = 0 := rfl

/-- Repeated completed CAR exchange: the first ladder is peeled through an arbitrary tail. -/
theorem operator_comp_operatorProduct_eq_thermalPeelSum
    (C₁ : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    C₁.operator.comp (operatorProduct l) =
      thermalPeelSum C₁ l + ((-1 : ℂ) ^ l.length) • ((operatorProduct l).comp C₁.operator) := by
  induction l with
  | nil =>
      simp [thermalPeelSum]
  | cons D t ih =>
      apply ContinuousLinearMap.ext
      intro ψ
      have hcar := DFunLike.congr_fun (completedAnticomm_operator_operator C₁ D) (operatorProduct t ψ)
      simp only [completedAnticomm_apply, smul_apply, ContinuousLinearMap.id_apply] at hcar
      have hexchange :
          C₁.operator (D.operator (operatorProduct t ψ)) =
            C₁.anticommutatorValue D • operatorProduct t ψ -
              D.operator (C₁.operator (operatorProduct t ψ)) :=
        eq_sub_of_add_eq hcar
      have hih := DFunLike.congr_fun ih ψ
      simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply] at hih
      simp only [operatorProduct_cons, thermalPeelSum, List.length_cons,
        ContinuousLinearMap.comp_apply, add_apply, sub_apply, smul_apply]
      rw [hexchange, hih]
      simp only [map_add, map_smul, pow_succ]
      module

/-- Canonical completed free-Gibbs expectation of an ordered thermal-ladder list. -/
noncomputable def completedFreeGibbsExpectation
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (l : List (CompletedThermalLadder Mode)) : ℂ :=
  (purePointGibbsDensityOperator completedOccupationHilbertBasis
    (fermionEnergy ε) β hsum).expectation (operatorProduct l)

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
      (purePointGibbsDensityOperator completedOccupationHilbertBasis
        (fermionEnergy ε) β hsum).expectation (thermalPeelSum C₁ l) +
        ((-1 : ℂ) ^ l.length) * completedFreeGibbsExpectation ε β hsum (l ++ [C₁]) := by
  rw [completedFreeGibbsExpectation, operatorProduct_cons,
    operator_comp_operatorProduct_eq_thermalPeelSum C₁ l]
  rw [map_add, map_smul]
  simp only [smul_eq_mul]
  rw [completedFreeGibbsExpectation, operatorProduct_append]
  simp

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization
