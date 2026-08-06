import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.TwoPoint

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Normalized free-boson two-point Gibbs identity

This module connects the summability-aware unnormalized two-point trace identity to the normalized
free Gibbs functional introduced for the convergence-aware bosonic thermal line.

The composite observable's membership in `freeGibbsDomain` remains an explicit hypothesis.  The
result therefore does not hide the analytic product-closure obligation needed by later Wick and
Dyson constructions.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode] [DecidableEq Mode]

/-- The normalized free-boson annihilation/creation two-point equation, together with the explicit
analytic-domain witness for the composite observable. -/
theorem freeGibbsExpectation_annihilate_comp_create
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i j : Mode)
    (hSumm : freeGibbsSummable ε β ((annihilate i).comp (create j))) :
    ((annihilate i).comp (create j) ∈ freeGibbsDomain ε β) ∧
      (1 - Complex.exp ((-(ε i) * β : ℝ) : ℂ)) *
          freeGibbsExpectation ε β ((annihilate i).comp (create j)) =
        if i = j then (1 : ℂ) else 0 := by
  refine ⟨hSumm, ?_⟩
  have htrace :=
    tsumTrace_imaginaryTimeEvolveFree_comp_annihilate_comp_create ε β hpos i j
  have hZ := freeGibbsPartition_ne_zero ε β hpos
  unfold freeGibbsExpectation
  rw [← mul_div_assoc]
  apply (div_eq_iff hZ).2
  simpa [freeGibbsPartition] using htrace

/-- The same normalized two-point equation stated through the convergence-aware functional adapter.
The domain witness is consumed by `value_of_mem`, so no out-of-domain totalization branch is used. -/
theorem freeGibbsFunctional_value_annihilate_comp_create
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i j : Mode)
    (hSumm : freeGibbsSummable ε β ((annihilate i).comp (create j))) :
    (1 - Complex.exp ((-(ε i) * β : ℝ) : ℂ)) *
        (freeGibbsFunctional ε β hpos).value ((annihilate i).comp (create j)) =
      if i = j then (1 : ℂ) else 0 := by
  rw [(freeGibbsFunctional ε β hpos).value_of_mem hSumm]
  change (1 - Complex.exp ((-(ε i) * β : ℝ) : ℂ)) *
      freeGibbsExpectation ε β ((annihilate i).comp (create j)) = _
  exact (freeGibbsExpectation_annihilate_comp_create ε β hpos i j hSumm).2

/-- The free two-point value in divided form.  The denominator's nonvanishing is kept explicit so
this statement can be reused by convergence-aware Wick data without hiding the analytic input. -/
theorem freeGibbsExpectation_annihilate_comp_create_eq
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i j : Mode)
    (hSumm : freeGibbsSummable ε β ((annihilate i).comp (create j)))
    (hden : 1 - Complex.exp ((-(ε i) * β : ℝ) : ℂ) ≠ 0) :
    freeGibbsExpectation ε β ((annihilate i).comp (create j)) =
      (if i = j then (1 : ℂ) else 0) /
        (1 - Complex.exp ((-(ε i) * β : ℝ) : ℂ)) := by
  apply (eq_div_iff hden).2
  rw [mul_comm]
  exact (freeGibbsExpectation_annihilate_comp_create ε β hpos i j hSumm).2

/-- Divided free two-point value through the total expectation adapter, restricted by the explicit
summability witness. -/
theorem freeGibbsFunctional_value_annihilate_comp_create_eq
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i j : Mode)
    (hSumm : freeGibbsSummable ε β ((annihilate i).comp (create j)))
    (hden : 1 - Complex.exp ((-(ε i) * β : ℝ) : ℂ) ≠ 0) :
    (freeGibbsFunctional ε β hpos).value ((annihilate i).comp (create j)) =
      (if i = j then (1 : ℂ) else 0) /
        (1 - Complex.exp ((-(ε i) * β : ℝ) : ℂ)) := by
  rw [(freeGibbsFunctional ε β hpos).value_of_mem hSumm]
  exact freeGibbsExpectation_annihilate_comp_create_eq ε β hpos i j hSumm hden

end
end Bosonic
end SecondQuantization
