import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Interaction
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.TotalParticleNumberWeightSummable

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Total-particle-number bound for a bosonic quartic vertex

A product of two annihilation and two creation operators has matrix coefficients growing at most
quadratically with the total occupation number.  This file proves the uniform bound needed to put a
single quartic vertex into the convergence-aware free Gibbs domain.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- Every mode occupation is bounded by the total particle number. -/
private theorem occupation_le_particleNumber (n : Occupation Mode) (i : Mode) :
    n i ≤ particleNumber n := by
  rw [particleNumber_eq_sum_univ]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)

/-- Four square-root ladder factors bounded by the same nonnegative number have product bounded by
its square. -/
private theorem sqrt_four_mul_le_sq {a b c d R : ℝ}
    (hR0 : 0 ≤ R) (ha : a ≤ R) (hb : b ≤ R) (hc : c ≤ R) (hd : d ≤ R) :
    Real.sqrt a * Real.sqrt b * Real.sqrt c * Real.sqrt d ≤ R ^ 2 := by
  have hsa : Real.sqrt a ≤ Real.sqrt R := Real.sqrt_le_sqrt ha
  have hsb : Real.sqrt b ≤ Real.sqrt R := Real.sqrt_le_sqrt hb
  have hsc : Real.sqrt c ≤ Real.sqrt R := Real.sqrt_le_sqrt hc
  have hsd : Real.sqrt d ≤ Real.sqrt R := Real.sqrt_le_sqrt hd
  have hab : Real.sqrt a * Real.sqrt b ≤ R := by
    calc
      Real.sqrt a * Real.sqrt b ≤ Real.sqrt R * Real.sqrt R :=
        mul_le_mul hsa hsb (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = R := by rw [← pow_two, Real.sq_sqrt hR0]
  have hcd : Real.sqrt c * Real.sqrt d ≤ R := by
    calc
      Real.sqrt c * Real.sqrt d ≤ Real.sqrt R * Real.sqrt R :=
        mul_le_mul hsc hsd (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = R := by rw [← pow_two, Real.sq_sqrt hR0]
  calc
    Real.sqrt a * Real.sqrt b * Real.sqrt c * Real.sqrt d =
        (Real.sqrt a * Real.sqrt b) * (Real.sqrt c * Real.sqrt d) := by ring
    _ ≤ R * R := mul_le_mul hab hcd (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hR0
    _ = R ^ 2 := by ring

/-- The diagonal coefficient of a single ordered bosonic quartic vertex is bounded uniformly by
`(N + 2)^2`, where `N` is the total occupation of the input basis state. -/
theorem norm_matrixCoeff_quarticVertexOperator_le (q : QuarticVertexLabel Mode)
    (n : Occupation Mode) :
    ‖Common.matrixCoeff (quarticVertexOperator q) n n‖ ≤ ((particleNumber n : ℝ) + 2) ^ 2 := by
  classical
  unfold Common.matrixCoeff
  change ‖(quarticVertexOperator q (basisState n)) n‖ ≤ ((particleNumber n : ℝ) + 2) ^ 2
  by_cases h1 : n q.annihilate₁ = 0
  · simp only [quarticVertexOperator, Common.quarticVertexOperator, LinearMap.comp_apply]
    rw [annihilate_basisState_of_zero h1]
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, norm_zero]
    positivity
  · let n1 := removeOccupation q.annihilate₁ n
    have hN1 : particleNumber n1 + 1 = particleNumber n := by
      simpa [n1] using particleNumber_removeOccupation_of_pos h1
    by_cases h2 : n1 q.annihilate₂ = 0
    · simp only [quarticVertexOperator, Common.quarticVertexOperator, LinearMap.comp_apply]
      rw [annihilate_basisState_of_pos h1, map_smul]
      change ‖(create q.create₁
        (create q.create₂ ((Real.sqrt (n q.annihilate₁ : ℝ) : ℂ) •
          annihilate q.annihilate₂ (basisState n1)))) n‖ ≤ _
      rw [annihilate_basisState_of_zero h2]
      simp only [smul_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply, norm_zero]
      positivity
    · let n2 := removeOccupation q.annihilate₂ n1
      let n3 := createOccupation q.create₂ n2
      let n4 := createOccupation q.create₁ n3
      have hN2 : particleNumber n2 + 1 = particleNumber n1 := by
        simpa [n2] using particleNumber_removeOccupation_of_pos h2
      have hN3 : particleNumber n3 = particleNumber n2 + 1 := by
        simp [n3]
      have ha1N : n q.annihilate₁ ≤ particleNumber n := occupation_le_particleNumber n _
      have ha2N : n1 q.annihilate₂ ≤ particleNumber n1 := occupation_le_particleNumber n1 _
      have hc2N : n2 q.create₂ ≤ particleNumber n2 := occupation_le_particleNumber n2 _
      have hc1N : n3 q.create₁ ≤ particleNumber n3 := occupation_le_particleNumber n3 _
      have ha1 : (n q.annihilate₁ : ℝ) ≤ (particleNumber n : ℝ) + 2 := by
        exact_mod_cast (show n q.annihilate₁ ≤ particleNumber n + 2 by omega)
      have ha2 : (n1 q.annihilate₂ : ℝ) ≤ (particleNumber n : ℝ) + 2 := by
        exact_mod_cast (show n1 q.annihilate₂ ≤ particleNumber n + 2 by omega)
      have hc2 : (n2 q.create₂ : ℝ) + 1 ≤ (particleNumber n : ℝ) + 2 := by
        exact_mod_cast (show n2 q.create₂ + 1 ≤ particleNumber n + 2 by omega)
      have hc1 : (n3 q.create₁ : ℝ) + 1 ≤ (particleNumber n : ℝ) + 2 := by
        exact_mod_cast (show n3 q.create₁ + 1 ≤ particleNumber n + 2 by omega)
      have hR0 : 0 ≤ (particleNumber n : ℝ) + 2 := by positivity
      have hsqrt := sqrt_four_mul_le_sq hR0 ha1 ha2 hc2 hc1
      let r : ℝ :=
        Real.sqrt (n q.annihilate₁ : ℝ) *
          (Real.sqrt (n1 q.annihilate₂ : ℝ) *
            (Real.sqrt (n2 q.create₂ + 1 : ℝ) *
              Real.sqrt (n3 q.create₁ + 1 : ℝ)))
      have hr0 : 0 ≤ r := by
        dsimp [r]
        positivity
      have hscalar :
          (Real.sqrt (n q.annihilate₁ : ℝ) : ℂ) *
              ((Real.sqrt (n1 q.annihilate₂ : ℝ) : ℂ) *
                ((Real.sqrt (n2 q.create₂ + 1 : ℝ) : ℂ) *
                  (Real.sqrt (n3 q.create₁ + 1 : ℝ) : ℂ))) = (r : ℂ) := by
        norm_cast
        simp [r]
      have haction : quarticVertexOperator q (basisState n) =
          (r : ℂ) • basisState n4 := by
        simp only [quarticVertexOperator, Common.quarticVertexOperator, LinearMap.comp_apply]
        rw [annihilate_basisState_of_pos h1, map_smul]
        change create q.create₁
          (create q.create₂ ((Real.sqrt (n q.annihilate₁ : ℝ) : ℂ) •
            annihilate q.annihilate₂ (basisState n1))) = _
        rw [annihilate_basisState_of_pos h2]
        simp only [map_smul]
        rw [create_basisState_eq]
        simp only [map_smul]
        rw [create_basisState_eq]
        simp only [smul_smul]
        change ((Real.sqrt (n q.annihilate₁ : ℝ) : ℂ) *
            ((Real.sqrt (n1 q.annihilate₂ : ℝ) : ℂ) *
              ((Real.sqrt (n2 q.create₂ + 1 : ℝ) : ℂ) *
                (Real.sqrt (n3 q.create₁ + 1 : ℝ) : ℂ)))) • basisState n4 = _
        rw [hscalar]
      rw [haction]
      by_cases hn4 : n4 = n
      · have hself : ((r : ℂ) • basisState n4) n = (r : ℂ) := by
          change ((r : ℂ) • Common.basisState n4) n = (r : ℂ)
          rw [hn4]
          exact Common.smul_basisState_apply_self (r : ℂ) n
        rw [hself, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
        calc
          r = Real.sqrt (n q.annihilate₁ : ℝ) *
              Real.sqrt (n1 q.annihilate₂ : ℝ) *
              Real.sqrt (n2 q.create₂ + 1 : ℝ) *
              Real.sqrt (n3 q.create₁ + 1 : ℝ) := by
                dsimp [r]
                ring
          _ ≤ ((particleNumber n : ℝ) + 2) ^ 2 := hsqrt
      · have hz : ((r : ℂ) • basisState n4) n = 0 := by
          change ((r : ℂ) • Common.basisState n4) n = 0
          exact Common.smul_basisState_apply_of_ne _ hn4
        rw [hz, norm_zero]
        positivity

end
end Bosonic
end SecondQuantization
