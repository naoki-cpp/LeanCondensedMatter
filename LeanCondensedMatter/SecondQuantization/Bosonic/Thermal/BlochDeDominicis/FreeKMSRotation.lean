import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.LadderTraceCyclicity
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreeThermalField
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-boson Gibbs KMS rotation

This module is the Bosonic Gibbs/KMS adapter. It combines the algebraic imaginary-time shift of a
creation or annihilation operator with the lower-level ladder `tsumTrace` cyclicity proved in
`Bosonic.Algebra.LadderTraceCyclicity`, then exposes normalized rotation and the uniform
`FreeThermalField` KMS factor used by the Bloch–de Dominicis recursion.

Occupation-coordinate formulas and reindexing proofs do not live here.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*}

private theorem tsumTrace_rotate_of_comp_eq_smul
    (D C A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (q : ℂ)
    (hmove : D.comp C = q • (C.comp D))
    (hcyclic : Common.tsumTrace (C.comp (D.comp A)) =
      Common.tsumTrace ((D.comp A).comp C)) :
    Common.tsumTrace (D.comp (C.comp A)) =
      q * Common.tsumTrace (D.comp (A.comp C)) := by
  rw [← LinearMap.comp_assoc D C A, hmove, LinearMap.smul_comp,
    Common.tsumTrace_smul, LinearMap.comp_assoc C D A, hcyclic,
    LinearMap.comp_assoc D A C]

/-- The KMS factor of a free thermal field. -/
noncomputable def FreeThermalField.kmsFactor (ε : Mode → ℝ) (β : ℝ) :
    FreeThermalField Mode → ℂ
  | .annihilate i => Complex.exp ((β : ℂ) * (ε i : ℂ))
  | .create i => Complex.exp (-(β : ℂ) * (ε i : ℂ))

/-- Uniform KMS rotation for either kind of free thermal field. -/
theorem FreeThermalField.freeGibbsExpectation_operator_comp_rotate
    (ε : Mode → ℝ) (β : ℝ) (C : FreeThermalField Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β (C.operator.comp A) =
      C.kmsFactor ε β * freeGibbsExpectation ε β (A.comp C.operator) := by
  have hmove :
      (imaginaryTimeEvolveFree ε (-β)).comp C.operator =
        C.kmsFactor ε β • (C.operator.comp (imaginaryTimeEvolveFree ε (-β))) := by
    cases C with
    | annihilate i =>
        simpa only [FreeThermalField.operator, FreeThermalField.kmsFactor,
          Complex.ofReal_neg, neg_neg] using imaginaryTimeEvolveFree_comp_annihilate ε (-β) i
    | create i =>
        simpa only [FreeThermalField.operator, FreeThermalField.kmsFactor,
          Complex.ofReal_neg] using imaginaryTimeEvolveFree_comp_create ε (-β) i
  have hcyclic :
      Common.tsumTrace (C.operator.comp ((imaginaryTimeEvolveFree ε (-β)).comp A)) =
        Common.tsumTrace (((imaginaryTimeEvolveFree ε (-β)).comp A).comp C.operator) := by
    cases C with
    | annihilate i => exact tsumTrace_annihilate_comp i _
    | create i => exact tsumTrace_create_comp i _
  unfold freeGibbsExpectation
  rw [tsumTrace_rotate_of_comp_eq_smul _ _ _ _ hmove hcyclic, mul_div_assoc]

end
end Bosonic
end SecondQuantization
