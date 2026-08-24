import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CCR
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.TwoPoint

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# Uncutoff bosonic two-point function

This module instantiates the Common Bloch–de Dominicis two-point identity on the algebraic bosonic
Fock space. Since `Occupation Mode` is infinite even for finite `Mode`, the proof supplies explicit
summability results for the partition series and the rotated two-point double series.

The construction combines free imaginary-time evolution, the canonical commutation relations, and
particle-number-weighted Boltzmann summability.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqBosonicBlochDeDominicisTwoPoint : DecidableEq Mode :=
  Classical.decEq Mode

omit [Fintype Mode] in
/-- Bridge `Common.matrixCoeff` to the local occupation-basis notation. -/
private theorem matrixCoeff_eq (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (m n : Occupation Mode) : Common.matrixCoeff A m n = A (basisState n) m := rfl

omit [Fintype Mode] in
private theorem smul_basisState_apply_self (c : ℂ) (n : Occupation Mode) :
    (c • basisState n : FockSpace Mode) n = c :=
  Common.smul_basisState_apply_self c n

omit [Fintype Mode] in
private theorem smul_basisState_apply_of_ne (c : ℂ) {m n : Occupation Mode} (h : m ≠ n) :
    (c • basisState m : FockSpace Mode) n = 0 :=
  Common.smul_basisState_apply_of_ne c h

/-- The diagonal matrix coefficient of `e^{τH₀}` is its basis eigenvalue. -/
theorem matrixCoeff_imaginaryTimeEvolveFree_self (ε : Mode → ℝ) (τ : ℝ) (n : Occupation Mode) :
    Common.matrixCoeff (imaginaryTimeEvolveFree ε τ) n n =
      Complex.exp ((τ * freeEigenvalue ε n : ℝ) : ℂ) := by
  rw [matrixCoeff_eq, imaginaryTimeEvolveFree_basisState, smul_basisState_apply_self]

/-- The annihilation matrix coefficient against the corresponding lowered state. -/
theorem matrixCoeff_annihilate_removeOccupation (i : Mode) (n : Occupation Mode) :
    Common.matrixCoeff (annihilate i) (removeOccupation i n) n = (Real.sqrt (n i : ℝ) : ℂ) := by
  rw [matrixCoeff_eq]
  by_cases h : n i = 0
  · rw [annihilate_basisState_of_zero h, h]
    simp
  · rw [annihilate_basisState_of_pos h, smul_basisState_apply_self]

/-- The matrix coefficient of `e^{τH₀}a_i†` against the corresponding lowered state. -/
theorem matrixCoeff_imaginaryTimeEvolveFree_comp_create_removeOccupation
    (ε : Mode → ℝ) (τ : ℝ) (i : Mode) (n : Occupation Mode) :
    Common.matrixCoeff ((imaginaryTimeEvolveFree ε τ).comp (create i)) n (removeOccupation i n) =
      (Real.sqrt (n i : ℝ) : ℂ) * Complex.exp ((τ * freeEigenvalue ε n : ℝ) : ℂ) := by
  rw [matrixCoeff_eq, LinearMap.comp_apply, create_basisState_eq, map_smul,
    imaginaryTimeEvolveFree_basisState, smul_smul]
  by_cases h : n i = 0
  · have hrw : removeOccupation i n = n := by
      ext k
      rcases eq_or_ne k i with rfl | hk
      · rw [removeOccupation_apply_same, h]
      · rw [removeOccupation_apply_ne hk]
    have hne : createOccupation i (removeOccupation i n) ≠ n := by
      rw [hrw]
      intro heq
      have hc := createOccupation_apply_same i n
      rw [heq] at hc
      omega
    rw [smul_basisState_apply_of_ne _ hne, h]
    simp
  · have hcoordN : (removeOccupation i n) i + 1 = n i := by
      rw [removeOccupation_apply_same]; omega
    have hcoord : ((removeOccupation i n) i : ℝ) + 1 = (n i : ℝ) := by exact_mod_cast hcoordN
    rw [createOccupation_removeOccupation_of_pos h, hcoord, smul_basisState_apply_self]

/-- Mixed matrix coefficients vanish when the annihilation and creation modes differ. -/
theorem matrixCoeff_imaginaryTimeEvolveFree_comp_create_mul_matrixCoeff_annihilate_of_ne
    {i j : Mode} (h : i ≠ j) (ε : Mode → ℝ) (τ : ℝ) (n k : Occupation Mode) :
    Common.matrixCoeff ((imaginaryTimeEvolveFree ε τ).comp (create j)) n k *
      Common.matrixCoeff (annihilate i) k n = 0 := by
  by_cases hi : n i = 0
  · have hval : Common.matrixCoeff (annihilate i) k n = 0 := by
      rw [matrixCoeff_eq, annihilate_basisState_of_zero hi]
      simp
    rw [hval, mul_zero]
  · by_cases hk : k = removeOccupation i n
    · subst hk
      have hval : Common.matrixCoeff
          ((imaginaryTimeEvolveFree ε τ).comp (create j)) n (removeOccupation i n) = 0 := by
        rw [matrixCoeff_eq, LinearMap.comp_apply, create_basisState_eq, map_smul,
          imaginaryTimeEvolveFree_basisState, smul_smul]
        have hne : createOccupation j (removeOccupation i n) ≠ n := by
          intro heq
          have hc := createOccupation_apply_same j (removeOccupation i n)
          rw [heq, removeOccupation_apply_ne (Ne.symm h)] at hc
          omega
        rw [smul_basisState_apply_of_ne _ hne]
      rw [hval, zero_mul]
    · have hval : Common.matrixCoeff (annihilate i) k n = 0 := by
        rw [matrixCoeff_eq, annihilate_basisState_of_pos hi,
          smul_basisState_apply_of_ne _ (Ne.symm hk)]
      rw [hval, mul_zero]

/-- The rotated equal-mode two-point double series is summable. -/
theorem summable_imaginaryTimeEvolveFree_comp_create_mul_annihilate_diag
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i : Mode) :
    Summable (Function.uncurry (fun n k =>
      Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp (create i)) n k *
        Common.matrixCoeff (annihilate i) k n)) := by
  set F : Occupation Mode × Occupation Mode → ℂ := Function.uncurry (fun n k =>
    Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp (create i)) n k *
      Common.matrixCoeff (annihilate i) k n) with hFdef
  set g : Occupation Mode → Occupation Mode × Occupation Mode :=
    fun n => (n, removeOccupation i n) with hgdef
  have hginj : Function.Injective g := fun n n' heq => (Prod.mk.injEq .. ▸ heq).1
  have hvanish : ∀ x ∉ Set.range g, F x = 0 := by
    intro x hx
    by_cases hk : x.2 = removeOccupation i x.1
    · exact absurd ⟨x.1, by simp only [hgdef]; rw [← hk]⟩ hx
    · have hval : Common.matrixCoeff (annihilate i) x.2 x.1 = 0 := by
        by_cases hi : x.1 i = 0
        · rw [matrixCoeff_eq, annihilate_basisState_of_zero hi]; simp
        · rw [matrixCoeff_eq, annihilate_basisState_of_pos hi,
            smul_basisState_apply_of_ne _ (Ne.symm hk)]
      rw [hFdef]
      simp only [Function.uncurry, hval, mul_zero]
  have hcomp : F ∘ g = fun n => (n i : ℂ) *
      Complex.exp ((-β * freeEigenvalue ε n : ℝ) : ℂ) := by
    funext n
    rw [Function.comp_apply, hFdef, hgdef]
    simp only [Function.uncurry]
    rw [matrixCoeff_imaginaryTimeEvolveFree_comp_create_removeOccupation,
      matrixCoeff_annihilate_removeOccupation, mul_right_comm, sqrt_natCast_mul_self]
  rw [← hginj.summable_iff hvanish, hcomp]
  have h := (hasSum_particleNumber_boltzmannWeight ε β hpos i).mapL Complex.ofRealCLM
  have heq : (fun n : Occupation Mode => Complex.ofRealCLM ((n i : ℝ) * boltzmannWeight ε β n)) =
      fun n : Occupation Mode => (n i : ℂ) * Complex.exp ((-β * freeEigenvalue ε n : ℝ) : ℂ) := by
    funext n
    simp [Complex.ofRealCLM_apply, boltzmannWeight]
  rw [heq] at h
  exact h.summable

/-- The Boltzmann-weighted diagonal partition series is summable over `ℂ`. -/
theorem summable_imaginaryTimeEvolveFree_self (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i) :
    Summable (fun n : Occupation Mode =>
      Common.matrixCoeff (imaginaryTimeEvolveFree ε (-β)) n n) := by
  have h := (hasSum_boltzmannWeight ε β hpos).mapL Complex.ofRealCLM
  have heq : (fun n : Occupation Mode => Complex.ofRealCLM (boltzmannWeight ε β n)) =
      fun n : Occupation Mode => Common.matrixCoeff (imaginaryTimeEvolveFree ε (-β)) n n := by
    funext n
    rw [matrixCoeff_imaginaryTimeEvolveFree_self]
    simp [Complex.ofRealCLM_apply, boltzmannWeight]
  rw [heq] at h
  exact h.summable

/-- The uncutoff bosonic two-point identity obtained from the Common Bloch–de Dominicis base case.
For `i = j`, division by the nonzero partition sum gives
`⟨aᵢaᵢ†⟩_β = (1 - e^{-βεᵢ})⁻¹`; combining this with the number-operator reordering identity yields
the Bose–Einstein occupation number. -/
theorem tsumTrace_imaginaryTimeEvolveFree_comp_annihilate_comp_create
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i j : Mode) :
    (1 - Complex.exp ((-(ε i) * β : ℝ) : ℂ)) *
        Common.tsumTrace
          ((imaginaryTimeEvolveFree ε (-β)).comp ((annihilate i).comp (create j))) =
      (if i = j then (1 : ℂ) else 0) * Common.tsumTrace (imaginaryTimeEvolveFree ε (-β)) := by
  unfold imaginaryTimeEvolveFree
  have hC1 : Common.heisenbergEvolve (freeEigenvalue ε) (-β) (annihilate i) =
      Complex.exp ((-(ε i) * (-β) : ℝ) : ℂ) • annihilate i := by
    have h := imaginaryTimeEvolve_annihilate ε (-β) i
    rwa [show ((-(ε i) * (-β) : ℝ) : ℂ) = -((-β : ℝ) : ℂ) * (ε i : ℂ) by push_cast; ring]
  have hcomm : (annihilate i).comp (create j) -
      (1 : ℂ) • ((create j).comp (annihilate i)) =
        (if i = j then (1 : ℂ) else 0) •
          (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) := by
    rw [one_smul]
    have h := comm_annihilate_create i j
    rw [comm] at h
    rw [h]
    split_ifs <;> simp
  have hSummD := summable_imaginaryTimeEvolveFree_self ε β hpos
  by_cases hij : i = j
  · subst hij
    have h := summable_imaginaryTimeEvolveFree_comp_create_mul_annihilate_diag ε β hpos i
    have hthm := Common.tsumTrace_diagonalEvolution_comp_two_point (freeEigenvalue ε) β (-(ε i))
      (1 : ℂ) (if i = i then (1 : ℂ) else 0) (annihilate i) (create i) hC1 hcomm hSummD h
    simpa using hthm
  · have hzero : Function.uncurry (fun n k =>
        Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp (create j)) n k *
          Common.matrixCoeff (annihilate i) k n) = 0 := by
      funext p
      simp only [Function.uncurry, Pi.zero_apply]
      exact matrixCoeff_imaginaryTimeEvolveFree_comp_create_mul_matrixCoeff_annihilate_of_ne hij ε
        (-β) p.1 p.2
    have h : Summable (Function.uncurry (fun n k =>
        Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp (create j)) n k *
          Common.matrixCoeff (annihilate i) k n)) := by
      rw [hzero]; exact summable_zero
    have hthm := Common.tsumTrace_diagonalEvolution_comp_two_point (freeEigenvalue ε) β (-(ε i))
      (1 : ℂ) (if i = j then (1 : ℂ) else 0) (annihilate i) (create j) hC1 hcomm hSummD h
    simpa using hthm

end
end Bosonic
end SecondQuantization
