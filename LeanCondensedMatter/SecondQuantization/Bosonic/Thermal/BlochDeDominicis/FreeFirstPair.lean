import Mathlib.Analysis.SpecialFunctions.Complex.Log
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeKMSRotation
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.OperatorPeel
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Module
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ConcretePairKernel

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-boson indexed peel and first-pair thermal reduction

This module proves the finite position-indexed bosonic peel formulas in the free-Gibbs domain,
then combines the bosonic CCR peel with the free-Gibbs KMS rotation.  Since the bosonic
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

/-! ## Indexed bosonic peel and Gibbs expectation -/

section IndexedPeel

variable {Mode : Type*}

namespace FreeThermalField

variable [Fintype Mode]

/-- The whole finite CCR peel is in the convergence-aware free-Gibbs domain. -/
theorem operatorPeelSum_mem_grandCanonicalGibbsDomain
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (C₁ : FreeThermalField Mode) (l : List (FreeThermalField Mode)) :
    C₁.operatorPeelSum l ∈ grandCanonicalGibbsDomain ε β μ := by
  simp only [operatorPeelSum, ScalarExchange.peelSum_eq_sum, one_pow, one_mul]
  refine Submodule.sum_mem (grandCanonicalGibbsDomain ε β μ) fun j _ => ?_
  exact (grandCanonicalGibbsDomain ε β μ).smul_mem
    (C₁.exchangeValue (l[(j : ℕ)]'j.isLt))
    (FreeThermalField.orderedProduct_mem_grandCanonicalGibbsDomain ε β μ hpos
      (l.eraseIdx j))

/-- Expectation of the bosonic CCR peel as a finite sum over the removed tail position. -/
theorem grandCanonicalGibbsExpectation_operatorPeelSum_eq_sum
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (C₁ : FreeThermalField Mode) (l : List (FreeThermalField Mode)) :
    grandCanonicalGibbsExpectation ε β μ (C₁.operatorPeelSum l) =
      ∑ j : Fin l.length,
        C₁.exchangeValue (l[(j : ℕ)]'j.isLt) *
          grandCanonicalGibbsExpectation ε β μ (orderedProduct (l.eraseIdx j)) := by
  simp only [operatorPeelSum, ScalarExchange.peelSum_eq_sum, one_pow, one_mul]
  calc
    grandCanonicalGibbsExpectation ε β μ
        (∑ j : Fin l.length,
          C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j)) =
        ∑ j : Fin l.length,
          grandCanonicalGibbsExpectation ε β μ
            (C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j)) :=
      grandCanonicalGibbsExpectation_sum_of_summable ε β μ
        (fun j : Fin l.length =>
          C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j))
        (fun j =>
          (grandCanonicalGibbsDomain ε β μ).smul_mem
            (C₁.exchangeValue (l[(j : ℕ)]'j.isLt))
            (FreeThermalField.orderedProduct_mem_grandCanonicalGibbsDomain ε β μ hpos
              (l.eraseIdx j)))
    _ = ∑ j : Fin l.length,
        C₁.exchangeValue (l[(j : ℕ)]'j.isLt) *
          grandCanonicalGibbsExpectation ε β μ (orderedProduct (l.eraseIdx j)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [grandCanonicalGibbsExpectation, LinearMap.comp_smul,
        Common.tsumTrace_smul, mul_div_assoc]

end FreeThermalField

end IndexedPeel

variable {Mode : Type*} [Fintype Mode]

/-- File-local classical decidable equality for the concrete pair kernel. -/
local instance instDecidableEqFreeFirstPair : DecidableEq Mode := Classical.decEq Mode

namespace FreeThermalField

/-- Bosonic CCR exchange plus KMS rotation solves the wrapped term with factor `q / (q - 1)`. -/
theorem grandCanonicalGibbsExpectation_cons_eq_kmsRatio_mul_operatorPeelSum
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (C : FreeThermalField Mode) (l : List (FreeThermalField Mode)) :
    grandCanonicalGibbsExpectation ε β μ (orderedProduct (C :: l)) =
      (C.kmsFactor (fun i => ε i - μ) β / (C.kmsFactor (fun i => ε i - μ) β - 1)) *
        grandCanonicalGibbsExpectation ε β μ (C.operatorPeelSum l) := by
  set E : ℂ := grandCanonicalGibbsExpectation ε β μ (orderedProduct (C :: l))
  set P : ℂ := grandCanonicalGibbsExpectation ε β μ (C.operatorPeelSum l)
  set R : ℂ := grandCanonicalGibbsExpectation ε β μ ((orderedProduct l).comp C.operator)
  have hRmem : (orderedProduct l).comp C.operator ∈ grandCanonicalGibbsDomain ε β μ := by
    simpa [orderedProduct, List.map_append, List.prod_append, Module.End.mul_eq_comp]
      using (orderedProduct_mem_grandCanonicalGibbsDomain ε β μ hpos (l ++ [C]))
  have hPmem : C.operatorPeelSum l ∈ grandCanonicalGibbsDomain ε β μ :=
    operatorPeelSum_mem_grandCanonicalGibbsDomain ε β μ hpos C l
  have hpeel : E = P + R := by
    have hop := C.operator_comp_orderedProduct_eq_operatorPeelSum l
    calc
      E = grandCanonicalGibbsExpectation ε β μ
          (C.operatorPeelSum l + (orderedProduct l).comp C.operator) := by
        dsimp [E]
        rw [show orderedProduct (C :: l) = C.operator.comp (orderedProduct l) by rfl,
          hop]
      _ = P + R := by
        dsimp [P, R]
        unfold grandCanonicalGibbsExpectation
        rw [LinearMap.comp_add, Common.tsumTrace_add hPmem hRmem, add_div]
  have hkms : E = C.kmsFactor (fun i => ε i - μ) β * R := by
    change grandCanonicalGibbsExpectation ε β μ (C.operator.comp (orderedProduct l)) =
      C.kmsFactor (fun i => ε i - μ) β *
        grandCanonicalGibbsExpectation ε β μ ((orderedProduct l).comp C.operator)
    exact C.grandCanonicalGibbsExpectation_operator_comp_rotate ε β μ (orderedProduct l)
  have hden : C.kmsFactor (fun i => ε i - μ) β - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    cases C with
    | annihilate i =>
        intro heq
        have hre := Complex.re_eq_re_of_cexp_eq_cexp
          (heq.trans Complex.exp_zero.symm)
        exact (ne_of_gt (hpos i)) (by simpa using hre)
    | create i =>
        intro heq
        have hre := Complex.re_eq_re_of_cexp_eq_cexp
          (heq.trans Complex.exp_zero.symm)
        exact (neg_ne_zero.mpr (ne_of_gt (hpos i))) (by simpa using hre)
  exact ScalarExchange.eq_div_mul_of_eq_add_mul_of_eq_mul E P R 1 (C.kmsFactor (fun i => ε i - μ) β)
    (by simpa only [one_mul] using hpeel) hkms
    hden

/-- The KMS solution factor times the bare CCR exchange coefficient is exactly the grand-canonical
normalized two-field free thermal kernel. -/
theorem grandCanonicalKmsRatio_mul_exchangeValue_eq_freeThermalPairValue
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (C D : FreeThermalField Mode) :
    (C.kmsFactor (fun i => ε i - μ) β / (C.kmsFactor (fun i => ε i - μ) β - 1)) * C.exchangeValue D =
      freeThermalPairValue (fun i => ε i - μ) β C D := by
  have hfirst := grandCanonicalGibbsExpectation_cons_eq_kmsRatio_mul_operatorPeelSum
    ε β μ hpos C [D]
  have hpeel :
      grandCanonicalGibbsExpectation ε β μ (C.operatorPeelSum [D]) = C.exchangeValue D := by
    rw [grandCanonicalGibbsExpectation_operatorPeelSum_eq_sum ε β μ hpos C [D]]
    simp [grandCanonicalGibbsExpectation_id ε β μ hpos]
  have hpair := grandCanonicalGibbsExpectation_orderedProduct_pair_eq_freeThermalPairValue
    ε β μ hpos C D
  calc
    (C.kmsFactor (fun i => ε i - μ) β / (C.kmsFactor (fun i => ε i - μ) β - 1)) * C.exchangeValue D =
        (C.kmsFactor (fun i => ε i - μ) β / (C.kmsFactor (fun i => ε i - μ) β - 1)) *
          grandCanonicalGibbsExpectation ε β μ (C.operatorPeelSum [D]) := by rw [hpeel]
    _ = grandCanonicalGibbsExpectation ε β μ (orderedProduct [C, D]) := hfirst.symm
    _ = freeThermalPairValue (fun i => ε i - μ) β C D := hpair

end FreeThermalField

end
end Bosonic
end SecondQuantization
