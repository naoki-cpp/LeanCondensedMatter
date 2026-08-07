import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.NormalizedTwoPoint
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalCompositionMatrixCoeff

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Concrete mixed free-boson Gibbs contractions

The normalized two-point theorem previously kept summability of `aᵢ aⱼ†` and nonvanishing of the
Bose denominator as explicit hypotheses.  Both are automatic under the standard positive
one-mode Boltzmann exponent assumption.  This file proves that fact directly on the infinite
occupation space and obtains the KMS-rotated reverse contraction from the CCR and linearity of the
convergence-aware Gibbs functional.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality for mode comparisons in the concrete contractions. -/
local instance instDecidableEqConcreteMixedTwoPoint : DecidableEq Mode := Classical.decEq Mode

/-- The diagonal coefficient of `aᵢ aⱼ†` is `nᵢ + 1` for equal modes and zero otherwise. -/
theorem matrixCoeff_annihilate_comp_create_self
    (i j : Mode) (n : Occupation Mode) :
    Common.matrixCoeff ((annihilate i).comp (create j)) n n =
      if i = j then (n i : ℂ) + 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Common.matrixCoeff, LinearMap.comp_apply]
    change (annihilate i (create i (basisState n))) n = (n i : ℂ) + 1
    rw [annihilate_create_basisState_same]
    change (((n i : ℂ) + 1) • Common.basisState n) n = (n i : ℂ) + 1
    exact Common.smul_basisState_apply_self ((n i : ℂ) + 1) n
  · rw [if_neg hij, Common.matrixCoeff, LinearMap.comp_apply]
    change (annihilate i (create j (basisState n))) n = 0
    rw [create_basisState_eq, map_smul]
    by_cases hi : n i = 0
    · have hzero : createOccupation j n i = 0 := by
        rw [createOccupation_apply_ne hij]
        exact hi
      rw [annihilate_basisState_of_zero hzero, smul_zero]
      rfl
    · have hpos : createOccupation j n i ≠ 0 := by
        rw [createOccupation_apply_ne hij]
        exact hi
      rw [annihilate_basisState_of_pos hpos, smul_smul]
      have hne : removeOccupation i (createOccupation j n) ≠ n := by
        intro h
        have hj := congrArg (fun x : Occupation Mode => x j) h
        rw [removeOccupation_apply_ne (Ne.symm hij), createOccupation_apply_same] at hj
        omega
      exact Common.smul_basisState_apply_of_ne _ hne

/-- The diagonal coefficient of `aᵢ aⱼ†` grows at most linearly with occupation number. -/
theorem norm_matrixCoeff_annihilate_comp_create_self_le
    (i j : Mode) (n : Occupation Mode) :
    ‖Common.matrixCoeff ((annihilate i).comp (create j)) n n‖ ≤ (n i : ℝ) + 1 := by
  rw [matrixCoeff_annihilate_comp_create_self]
  split_ifs
  · have hcast : (n i : ℂ) + 1 = (((n i : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  · rw [norm_zero]
    positivity

variable [Fintype Mode]

/-- `aᵢ aⱼ†` has a summable free-Gibbs numerator under positive one-mode Boltzmann exponents. -/
theorem freeGibbsSummable_annihilate_comp_create
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i j : Mode) :
    freeGibbsSummable ε β ((annihilate i).comp (create j)) := by
  unfold freeGibbsSummable imaginaryTimeEvolveFree
  have hN := summable_particleNumber_boltzmannWeight ε β hpos i
  have hW := summable_boltzmannWeight ε β hpos
  have hmajorant : Summable (fun n : Occupation Mode =>
      (n i : ℝ) * boltzmannWeight ε β n + boltzmannWeight ε β n) := hN.add hW
  apply hmajorant.of_norm_bounded
  intro n
  rw [Common.matrixCoeff_diagonalEvolution_comp, norm_mul, Complex.norm_exp]
  have hA := norm_matrixCoeff_annihilate_comp_create_self_le i j n
  have hw : 0 ≤ boltzmannWeight ε β n := Real.exp_nonneg _
  change boltzmannWeight ε β n *
      ‖Common.matrixCoeff ((annihilate i).comp (create j)) n n‖ ≤ _
  calc
    boltzmannWeight ε β n * ‖Common.matrixCoeff ((annihilate i).comp (create j)) n n‖ ≤
        boltzmannWeight ε β n * ((n i : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hA hw
    _ = (n i : ℝ) * boltzmannWeight ε β n + boltzmannWeight ε β n := by ring

/-- Domain form of `freeGibbsSummable_annihilate_comp_create`. -/
theorem annihilate_comp_create_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i j : Mode) :
    (annihilate i).comp (create j) ∈ freeGibbsDomain ε β :=
  freeGibbsSummable_annihilate_comp_create ε β hpos i j

/-- The reverse mixed product `aⱼ† aᵢ` is also in the free-Gibbs domain.  This follows from the CCR
and linear closure, so no second occupation-space convergence proof is needed. -/
theorem create_comp_annihilate_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i j : Mode) :
    (create j).comp (annihilate i) ∈ freeGibbsDomain ε β := by
  have hA := annihilate_comp_create_mem_freeGibbsDomain ε β hpos i j
  by_cases hij : i = j
  · subst j
    have hId := linearMap_id_mem_freeGibbsDomain ε β hpos
    have hc := comm_annihilate_create i i
    rw [comm, if_pos rfl] at hc
    have hop : (create i).comp (annihilate i) =
        (annihilate i).comp (create i) -
          (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) := by
      calc
        (create i).comp (annihilate i) =
            (annihilate i).comp (create i) -
              ((annihilate i).comp (create i) - (create i).comp (annihilate i)) := by abel
        _ = (annihilate i).comp (create i) - LinearMap.id := by rw [hc]
    rw [hop]
    exact (freeGibbsDomain ε β).sub_mem hA hId
  · have hc := comm_annihilate_create i j
    rw [comm, if_neg hij] at hc
    have hop : (create j).comp (annihilate i) = (annihilate i).comp (create j) := by
      calc
        (create j).comp (annihilate i) =
            (annihilate i).comp (create j) -
              ((annihilate i).comp (create j) - (create j).comp (annihilate i)) := by abel
        _ = (annihilate i).comp (create j) := by rw [hc, sub_zero]
    rw [hop]
    exact hA

/-- Summability form for the reverse mixed product. -/
theorem freeGibbsSummable_create_comp_annihilate
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i j : Mode) :
    freeGibbsSummable ε β ((create j).comp (annihilate i)) :=
  create_comp_annihilate_mem_freeGibbsDomain ε β hpos i j

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
  have hSumm := freeGibbsSummable_annihilate_comp_create ε β hpos i j
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
  by_cases hij : i = j
  · subst j
    have hA := freeGibbsSummable_annihilate_comp_create ε β hpos i i
    have hId := linearMap_id_mem_freeGibbsDomain ε β hpos
    have hc := comm_annihilate_create i i
    rw [comm, if_pos rfl] at hc
    have hop : (create i).comp (annihilate i) =
        (annihilate i).comp (create i) -
          (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) := by
      calc
        (create i).comp (annihilate i) =
            (annihilate i).comp (create i) -
              ((annihilate i).comp (create i) - (create i).comp (annihilate i)) := by abel
        _ = (annihilate i).comp (create i) - LinearMap.id := by rw [hc]
    rw [if_pos rfl, hop, sub_eq_add_neg]
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
    simp only [if_true]
    have hden := freeGibbs_boseDenominator_ne_zero ε β hpos i
    have harg : (-(ε i) * β : ℝ) = -(ε i * β) := by ring
    rw [harg] at hden
    field_simp [hden]
    ring
  · have hc := comm_annihilate_create j i
    rw [comm, if_neg (Ne.symm hij)] at hc
    have hop : (create i).comp (annihilate j) = (annihilate j).comp (create i) := by
      calc
        (create i).comp (annihilate j) =
            (annihilate j).comp (create i) -
              ((annihilate j).comp (create i) - (create i).comp (annihilate j)) := by abel
        _ = (annihilate j).comp (create i) := by rw [hc, sub_zero]
    rw [if_neg hij, hop,
      freeGibbsExpectation_annihilate_comp_create_concrete ε β hpos j i]
    simp [Ne.symm hij]

end
end Bosonic
end SecondQuantization
