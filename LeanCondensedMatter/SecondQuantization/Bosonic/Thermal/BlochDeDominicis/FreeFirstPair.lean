import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreePeelIndexed
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ConcretePairKernel

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-boson first-pair thermal reduction

This file combines the bosonic CCR peel with the free-Gibbs KMS rotation.  Since the bosonic
exchange sign is `+1`, the wrapped term is solved with denominator `kmsFactor - 1`.  Under the
standard positivity hypothesis this denominator is nonzero for both annihilation and creation
fields.

The resulting scalar multiplying a bare CCR contraction is identified with the already concrete
normalized two-field kernel `freeThermalPairValue`; no separate closed-form thermal-factor proof is
needed.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- File-local classical decidable equality for the concrete pair kernel. -/
local instance instDecidableEqFreeFirstPair : DecidableEq Mode := Classical.decEq Mode

namespace FreeThermalField

omit [Fintype Mode] in
/-- Positive one-mode Boltzmann exponents keep the bosonic KMS denominator away from zero. -/
theorem kmsFactor_sub_one_ne_zero
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (C : FreeThermalField Mode) :
    C.kmsFactor ε β - 1 ≠ 0 := by
  cases C with
  | annihilate i =>
      intro hzero
      have hexp : Complex.exp ((β : ℂ) * (ε i : ℂ)) = 1 := sub_eq_zero.mp hzero
      have hnorm := congrArg norm hexp
      rw [Complex.norm_exp, norm_one] at hnorm
      have hre : (((β : ℂ) * (ε i : ℂ))).re = β * ε i := by simp
      rw [hre] at hnorm
      have hgt : 1 < Real.exp (β * ε i) := by
        rw [Real.one_lt_exp_iff]
        exact hpos i
      linarith
  | create i =>
      intro hzero
      have hexp : Complex.exp (-(β : ℂ) * (ε i : ℂ)) = 1 := sub_eq_zero.mp hzero
      have hnorm := congrArg norm hexp
      rw [Complex.norm_exp, norm_one] at hnorm
      have hre : ((-(β : ℂ) * (ε i : ℂ))).re = -(β * ε i) := by simp
      rw [hre] at hnorm
      have hlt : Real.exp (-(β * ε i)) < 1 := by
        rw [Real.exp_lt_one_iff]
        nlinarith [hpos i]
      linarith

omit [Fintype Mode] in
/-- Appending a free thermal field on the right agrees with postcomposition by its operator. -/
theorem orderedProduct_append_singleton
    (l : List (FreeThermalField Mode)) (C : FreeThermalField Mode) :
    orderedProduct (l ++ [C]) = (orderedProduct l).comp C.operator := by
  rw [orderedProduct_eq_common_operatorProduct,
    Common.BlochDeDominicis.operatorProduct_append,
    ← orderedProduct_eq_common_operatorProduct]
  simp

/-- Bosonic CCR exchange plus KMS rotation solves the wrapped term with factor `q / (q - 1)`. -/
theorem freeGibbsExpectation_cons_eq_kmsRatio_mul_operatorPeelSum
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (C : FreeThermalField Mode) (l : List (FreeThermalField Mode)) :
    freeGibbsExpectation ε β (orderedProduct (C :: l)) =
      (C.kmsFactor ε β / (C.kmsFactor ε β - 1)) *
        freeGibbsExpectation ε β (C.operatorPeelSum l) := by
  set E : ℂ := freeGibbsExpectation ε β (orderedProduct (C :: l))
  set P : ℂ := freeGibbsExpectation ε β (C.operatorPeelSum l)
  set R : ℂ := freeGibbsExpectation ε β ((orderedProduct l).comp C.operator)
  have hRmem : (orderedProduct l).comp C.operator ∈ freeGibbsDomain ε β := by
    rw [← orderedProduct_append_singleton]
    exact orderedProduct_mem_freeGibbsDomain ε β hpos (l ++ [C])
  have hPmem : C.operatorPeelSum l ∈ freeGibbsDomain ε β :=
    operatorPeelSum_mem_freeGibbsDomain ε β hpos C l
  have hpeel : E = P + R := by
    have hop := C.operator_comp_orderedProduct_eq_operatorPeelSum l
    calc
      E = freeGibbsExpectation ε β
          (C.operatorPeelSum l + (orderedProduct l).comp C.operator) := by
        dsimp [E]
        rw [show orderedProduct (C :: l) = C.operator.comp (orderedProduct l) by rfl,
          hop]
      _ = P + R := by
        rw [freeGibbsExpectation_add ε β hPmem hRmem]
  have hkms : E = C.kmsFactor ε β * R := by
    change freeGibbsExpectation ε β (C.operator.comp (orderedProduct l)) =
      C.kmsFactor ε β *
        freeGibbsExpectation ε β ((orderedProduct l).comp C.operator)
    exact C.freeGibbsExpectation_operator_comp_rotate ε β (orderedProduct l)
  have hqR : C.kmsFactor ε β * R = P + R := by
    calc
      C.kmsFactor ε β * R = E := hkms.symm
      _ = P + R := hpeel
  have hRmul : R * (C.kmsFactor ε β - 1) = P := by
    calc
      R * (C.kmsFactor ε β - 1) = C.kmsFactor ε β * R - R := by ring
      _ = (P + R) - R := by rw [hqR]
      _ = P := by ring
  have hne := C.kmsFactor_sub_one_ne_zero ε β hpos
  have hR : R = P / (C.kmsFactor ε β - 1) :=
    (eq_div_iff hne).2 hRmul
  calc
    freeGibbsExpectation ε β (orderedProduct (C :: l)) = E := rfl
    _ = C.kmsFactor ε β * R := hkms
    _ = (C.kmsFactor ε β / (C.kmsFactor ε β - 1)) * P := by
      rw [hR]
      ring
    _ = (C.kmsFactor ε β / (C.kmsFactor ε β - 1)) *
        freeGibbsExpectation ε β (C.operatorPeelSum l) := rfl

/-- The KMS solution factor times the bare CCR exchange coefficient is exactly the canonical
normalized two-field free thermal kernel. -/
theorem kmsRatio_mul_exchangeValue_eq_freeThermalPairValue
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (C D : FreeThermalField Mode) :
    (C.kmsFactor ε β / (C.kmsFactor ε β - 1)) * C.exchangeValue D =
      freeThermalPairValue ε β C D := by
  have hfirst := freeGibbsExpectation_cons_eq_kmsRatio_mul_operatorPeelSum
    ε β hpos C [D]
  have hpeel :
      freeGibbsExpectation ε β (C.operatorPeelSum [D]) = C.exchangeValue D := by
    rw [freeGibbsExpectation_operatorPeelSum_eq_sum ε β hpos C [D]]
    simp [freeGibbsExpectation_id ε β hpos]
  have hpair := freeGibbsExpectation_orderedProduct_pair_eq_freeThermalPairValue
    ε β hpos C D
  calc
    (C.kmsFactor ε β / (C.kmsFactor ε β - 1)) * C.exchangeValue D =
        (C.kmsFactor ε β / (C.kmsFactor ε β - 1)) *
          freeGibbsExpectation ε β (C.operatorPeelSum [D]) := by rw [hpeel]
    _ = freeGibbsExpectation ε β (orderedProduct [C, D]) := hfirst.symm
    _ = freeThermalPairValue ε β C D := hpair

end FreeThermalField

end
end Bosonic
end SecondQuantization
