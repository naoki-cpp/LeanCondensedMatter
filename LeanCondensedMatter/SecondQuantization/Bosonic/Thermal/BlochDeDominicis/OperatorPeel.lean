import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.OperatorPeel
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.OrderedProductSummable

set_option linter.style.header false

/-!
# Bosonic free-thermal operator peel

This file instantiates the Common scalar-exchange peel identity for the concrete free bosonic
creation/annihilation fields. The scalar here is the bare CCR contraction, not yet the normalized
thermal pair value. Combining this algebraic peel with the free-Gibbs KMS rotation is the remaining
step toward the analytic first-pair recurrence.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality for CCR contractions. -/
local instance instDecidableEqFreeThermalOperatorPeel : DecidableEq Mode := Classical.decEq Mode

/-- Bare scalar CCR contraction generated when the first free thermal field is exchanged past the
second. -/
noncomputable def FreeThermalField.exchangeValue :
    FreeThermalField Mode → FreeThermalField Mode → ℂ
  | .annihilate i, .create j => if i = j then 1 else 0
  | .create i, .annihilate j => if i = j then -1 else 0
  | .annihilate _, .annihilate _ => 0
  | .create _, .create _ => 0

/-- The concrete free bosonic fields satisfy the scalar exchange relation used by the Common peel
identity. -/
theorem FreeThermalField.operator_comp_operator_eq_exchangeValue
    (C D : FreeThermalField Mode) :
    (C.operator).comp D.operator =
      C.exchangeValue D • (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) +
        (D.operator).comp C.operator := by
  cases C with
  | annihilate i =>
      cases D with
      | annihilate j =>
          simp only [FreeThermalField.operator, FreeThermalField.exchangeValue,
            zero_smul, zero_add]
          have h := comm_annihilate_annihilate i j
          unfold comm at h
          exact sub_eq_zero.mp h
      | create j =>
          by_cases hij : i = j
          · subst j
            simp only [FreeThermalField.operator, FreeThermalField.exchangeValue, if_true, one_smul]
            have h := comm_annihilate_create i i
            rw [if_pos rfl] at h
            unfold comm at h
            exact (sub_eq_iff_eq_add).mp h
          · simp only [FreeThermalField.operator, FreeThermalField.exchangeValue,
              if_neg hij, zero_smul, zero_add]
            have h := comm_annihilate_create i j
            rw [if_neg hij] at h
            unfold comm at h
            exact sub_eq_zero.mp h
  | create i =>
      cases D with
      | annihilate j =>
          by_cases hij : i = j
          · subst j
            simp only [FreeThermalField.operator, FreeThermalField.exchangeValue,
              if_true, neg_one_smul]
            have h := comm_create_annihilate i i
            rw [if_pos rfl] at h
            unfold comm at h
            exact (sub_eq_iff_eq_add).mp h
          · simp only [FreeThermalField.operator, FreeThermalField.exchangeValue,
              if_neg hij, zero_smul, zero_add]
            have h := comm_create_annihilate i j
            rw [if_neg hij] at h
            unfold comm at h
            exact sub_eq_zero.mp h
      | create j =>
          simp only [FreeThermalField.operator, FreeThermalField.exchangeValue,
            zero_smul, zero_add]
          have h := comm_create_create i j
          unfold comm at h
          exact sub_eq_zero.mp h

/-- The bosonic ordered product is the Common right-associated operator product specialized to the
free thermal field operator map. -/
theorem FreeThermalField.orderedProduct_eq_common_operatorProduct
    (fields : List (FreeThermalField Mode)) :
    FreeThermalField.orderedProduct fields =
      Common.BlochDeDominicis.operatorProduct FreeThermalField.operator fields := by
  induction fields with
  | nil => rfl
  | cons C t ih =>
    simp only [FreeThermalField.orderedProduct,
        Common.BlochDeDominicis.operatorProduct_cons]
    rw [ih]

/-- Bare bosonic CCR peel sum, before Gibbs/KMS rotation. -/
noncomputable def FreeThermalField.operatorPeelSum (C : FreeThermalField Mode)
    (fields : List (FreeThermalField Mode)) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.BlochDeDominicis.operatorPeelSum FreeThermalField.operator
    FreeThermalField.exchangeValue 1 C fields

/-- Repeated CCR exchange of the first free thermal field through an arbitrary finite tail. -/
theorem FreeThermalField.operator_comp_orderedProduct_eq_operatorPeelSum
    (C : FreeThermalField Mode) (fields : List (FreeThermalField Mode)) :
    (C.operator).comp (FreeThermalField.orderedProduct fields) =
      C.operatorPeelSum fields +
        (FreeThermalField.orderedProduct fields).comp C.operator := by
  have h := Common.BlochDeDominicis.operator_comp_operatorProduct_eq_operatorPeelSum
    FreeThermalField.operator FreeThermalField.exchangeValue (1 : ℂ)
    (fun C D => by
      simpa using FreeThermalField.operator_comp_operator_eq_exchangeValue C D)
    C fields
  rw [← FreeThermalField.orderedProduct_eq_common_operatorProduct] at h
  simpa [FreeThermalField.operatorPeelSum] using h

end
end Bosonic
end SecondQuantization
