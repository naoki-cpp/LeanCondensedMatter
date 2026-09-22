import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.LadderTraceCyclicity
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeExpectationRecursion

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

/-- Unnormalized KMS rotation of an annihilation operator through the free Gibbs weight. -/
theorem freeGibbsTsum_annihilate_rotate (ε : Mode → ℝ) (β : ℝ) (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    Common.tsumTrace
        ((imaginaryTimeEvolveFree ε (-β)).comp ((annihilate i).comp A)) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) *
        Common.tsumTrace
          ((imaginaryTimeEvolveFree ε (-β)).comp (A.comp (annihilate i))) := by
  let D := imaginaryTimeEvolveFree ε (-β)
  let q : ℂ := Complex.exp ((β : ℂ) * (ε i : ℂ))
  have hmove : D.comp (annihilate i) = q • ((annihilate i).comp D) := by
    dsimp [D, q]
    have h := imaginaryTimeEvolveFree_comp_annihilate ε (-β) i
    have hexp : -((-β : ℝ) : ℂ) * (ε i : ℂ) = (β : ℂ) * (ε i : ℂ) := by
      push_cast
      ring
    rwa [hexp] at h
  calc
    Common.tsumTrace (D.comp ((annihilate i).comp A)) =
        Common.tsumTrace ((D.comp (annihilate i)).comp A) := by
      rw [LinearMap.comp_assoc]
    _ = Common.tsumTrace ((q • ((annihilate i).comp D)).comp A) := by rw [hmove]
    _ = Common.tsumTrace (q • (((annihilate i).comp D).comp A)) := by
      rw [LinearMap.smul_comp]
    _ = q * Common.tsumTrace (((annihilate i).comp D).comp A) :=
      Common.tsumTrace_smul q (((annihilate i).comp D).comp A)
    _ = q * Common.tsumTrace ((annihilate i).comp (D.comp A)) := by
      rw [LinearMap.comp_assoc]
    _ = q * Common.tsumTrace ((D.comp A).comp (annihilate i)) := by
      rw [tsumTrace_annihilate_comp]
    _ = q * Common.tsumTrace (D.comp (A.comp (annihilate i))) := by
      rw [LinearMap.comp_assoc]

/-- Unnormalized KMS rotation of a creation operator through the free Gibbs weight. -/
theorem freeGibbsTsum_create_rotate (ε : Mode → ℝ) (β : ℝ) (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    Common.tsumTrace
        ((imaginaryTimeEvolveFree ε (-β)).comp ((create i).comp A)) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
        Common.tsumTrace
          ((imaginaryTimeEvolveFree ε (-β)).comp (A.comp (create i))) := by
  let D := imaginaryTimeEvolveFree ε (-β)
  let q : ℂ := Complex.exp (-(β : ℂ) * (ε i : ℂ))
  have hmove : D.comp (create i) = q • ((create i).comp D) := by
    dsimp [D, q]
    have h := imaginaryTimeEvolveFree_comp_create ε (-β) i
    have hexp : (((-β : ℝ) : ℂ) * (ε i : ℂ)) = -(β : ℂ) * (ε i : ℂ) := by
      push_cast
      ring
    rwa [hexp] at h
  calc
    Common.tsumTrace (D.comp ((create i).comp A)) =
        Common.tsumTrace ((D.comp (create i)).comp A) := by
      rw [LinearMap.comp_assoc]
    _ = Common.tsumTrace ((q • ((create i).comp D)).comp A) := by rw [hmove]
    _ = Common.tsumTrace (q • (((create i).comp D).comp A)) := by
      rw [LinearMap.smul_comp]
    _ = q * Common.tsumTrace (((create i).comp D).comp A) :=
      Common.tsumTrace_smul q (((create i).comp D).comp A)
    _ = q * Common.tsumTrace ((create i).comp (D.comp A)) := by
      rw [LinearMap.comp_assoc]
    _ = q * Common.tsumTrace ((D.comp A).comp (create i)) := by
      rw [tsumTrace_create_comp]
    _ = q * Common.tsumTrace (D.comp (A.comp (create i))) := by
      rw [LinearMap.comp_assoc]

/-- Normalized free-Gibbs KMS rotation for annihilation. -/
theorem freeGibbsExpectation_annihilate_rotate (ε : Mode → ℝ) (β : ℝ) (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β ((annihilate i).comp A) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) *
        freeGibbsExpectation ε β (A.comp (annihilate i)) := by
  unfold freeGibbsExpectation
  rw [freeGibbsTsum_annihilate_rotate, mul_div_assoc]

/-- Normalized free-Gibbs KMS rotation for creation. -/
theorem freeGibbsExpectation_create_rotate (ε : Mode → ℝ) (β : ℝ) (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β ((create i).comp A) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
        freeGibbsExpectation ε β (A.comp (create i)) := by
  unfold freeGibbsExpectation
  rw [freeGibbsTsum_create_rotate, mul_div_assoc]

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
  cases C with
  | annihilate i =>
      exact freeGibbsExpectation_annihilate_rotate ε β i A
  | create i =>
      exact freeGibbsExpectation_create_rotate ε β i A

end
end Bosonic
end SecondQuantization
