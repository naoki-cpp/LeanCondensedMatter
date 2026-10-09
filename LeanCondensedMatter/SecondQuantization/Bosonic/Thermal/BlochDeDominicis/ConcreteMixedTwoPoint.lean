import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.NormalizedTwoPoint
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.OrderedProductSummable

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Concrete mixed free-boson Gibbs contractions

Under the standard positive one-mode Boltzmann exponent assumption, summability of the mixed product
`aᵢ aⱼ†` follows from the general finite ordered-product summability theorem on the infinite
occupation space. The Bose denominator is nonzero under the same positivity hypothesis. The reverse
contraction follows from the canonical commutation relation and linearity on the free-Gibbs domain.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality for mode comparisons in the concrete contractions. -/
local instance instDecidableEqConcreteMixedTwoPoint : DecidableEq Mode := Classical.decEq Mode

variable [Fintype Mode]

omit [Fintype Mode] in
/-- The Bose denominator is nonzero under the same positivity hypothesis that makes the partition
series converge. -/
theorem freeGibbs_boseDenominator_ne_zero
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i : Mode) :
    1 - Complex.exp (((-(ε i) * β : ℝ) : ℂ)) ≠ 0 := by
  intro hzero
  have hexp : Complex.exp (((-(ε i) * β : ℝ) : ℂ)) = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm := congrArg norm hexp
  rw [Complex.norm_exp, norm_one] at hnorm
  have hre : (((-(ε i) * β : ℝ) : ℂ)).re = -(ε i) * β := rfl
  rw [hre] at hnorm
  have hlt : Real.exp (-(ε i) * β) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [hpos i]
  linarith

/-- Concrete normalized annihilation/creation contraction. -/
theorem freeGibbsExpectation_annihilate_comp_create_concrete
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i j : Mode) :
    freeGibbsExpectation ε β ((annihilate i).comp (create j)) =
      if i = j then (1 - Complex.exp (((-(ε i) * β : ℝ) : ℂ)))⁻¹ else 0 := by
  have hSumm : freeGibbsSummable ε β ((annihilate i).comp (create j)) := by
    simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
      Module.End.mul_eq_comp] using
      (FreeThermalField.freeGibbsSummable_orderedProduct ε β hpos
        [.annihilate i, .create j])
  have hden := freeGibbs_boseDenominator_ne_zero ε β hpos i
  rw [freeGibbsExpectation_annihilate_comp_create_eq ε β hpos i j hSumm hden]
  by_cases hij : i = j <;> simp [hij]

/-- Concrete KMS-rotated creation/annihilation contraction. -/
theorem freeGibbsExpectation_create_comp_annihilate_concrete
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i j : Mode) :
    freeGibbsExpectation ε β ((create i).comp (annihilate j)) =
      if i = j then
        Complex.exp (((-(ε j) * β : ℝ) : ℂ)) *
          (1 - Complex.exp (((-(ε j) * β : ℝ) : ℂ)))⁻¹
      else 0 := by
  have hreorder :
      (annihilate j).comp (create i) =
        (if j = i then (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) else 0) +
          (create i).comp (annihilate j) := by
    simpa [Module.End.mul_eq_comp] using
      (ScalarExchange.mul_eq_add_smul_mul_of_zetaCommutator_eq (1 : ℂ)
        (comm_annihilate_create j i))
  by_cases hij : i = j
  · subst j
    have hA : freeGibbsSummable ε β ((annihilate i).comp (create i)) := by
      simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
        Module.End.mul_eq_comp] using
        (FreeThermalField.freeGibbsSummable_orderedProduct ε β hpos
          [.annihilate i, .create i])
    have hId := linearMap_id_mem_freeGibbsDomain ε β hpos
    have hop : (create i).comp (annihilate i) =
        (annihilate i).comp (create i) -
          (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) := by
      apply (eq_sub_iff_add_eq).2
      simpa [add_comm] using hreorder.symm
    rw [ite_eq_left rfl, hop, sub_eq_add_neg]
    have hnegId : -(LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) ∈
        freeGibbsDomain ε β := (freeGibbsDomain ε β).neg_mem hId
    rw [freeGibbsExpectation_add ε β hA hnegId]
    have hnegExpectation :
        freeGibbsExpectation ε β
            (-(LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode)) = -1 := by
      rw [show -(LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) =
          (-1 : ℂ) • (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) by simp,
        freeGibbsExpectation_smul, freeGibbsExpectation_id ε β hpos]
      ring
    rw [hnegExpectation,
      freeGibbsExpectation_annihilate_comp_create_concrete ε β hpos i i]
    simp only [ite_true]
    have hden := freeGibbs_boseDenominator_ne_zero ε β hpos i
    have harg : (-(ε i) * β : ℝ) = -(ε i * β) := by ring
    rw [harg] at hden
    field_simp [hden]
    ring
  · have hop : (create i).comp (annihilate j) = (annihilate j).comp (create i) := by
      simpa [Ne.symm hij] using hreorder.symm
    rw [ite_eq_right hij, hop,
      freeGibbsExpectation_annihilate_comp_create_concrete ε β hpos j i]
    simp [Ne.symm hij]

end
end Bosonic
end SecondQuantization
