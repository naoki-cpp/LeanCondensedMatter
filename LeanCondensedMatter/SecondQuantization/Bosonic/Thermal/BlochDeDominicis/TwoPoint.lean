import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CCR
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Summability for the uncutoff bosonic two-point function

Since `Occupation Mode` is infinite even for finite `Mode`, this module supplies summability
results for the partition series and the rotated two-point double series. ConcreteMixedTwoPoint
uses these results to instantiate the Common normalized summable trace identity.

The estimates combine free imaginary-time evolution and particle-number-weighted Boltzmann
summability.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqBosonicBlochDeDominicisTwoPoint : DecidableEq Mode :=
  Classical.decEq Mode

omit [Fintype Mode] in
/-- The diagonal matrix coefficient of `e^{τH₀}` is its basis eigenvalue. -/
theorem matrixCoeff_imaginaryTimeEvolveFree_self (ε : Mode → ℝ) (τ : ℝ) (n : Occupation Mode) :
    Common.matrixCoeff (imaginaryTimeEvolveFree ε τ) n n =
      Complex.exp ((τ * freeEigenvalue ε n : ℝ) : ℂ) := by
  simpa using
    (Common.matrixCoeff_eq_ite_of_basisState_smul
      (m := n) (imaginaryTimeEvolveFree_basisState ε τ n))

omit [Fintype Mode] in
/-- The matrix coefficient of `e^{τH₀}a_i†` against the corresponding lowered state. -/
private theorem matrixCoeff_imaginaryTimeEvolveFree_comp_create_removeOccupation
    (ε : Mode → ℝ) (τ : ℝ) (i : Mode) (n : Occupation Mode) :
    Common.matrixCoeff ((imaginaryTimeEvolveFree ε τ).comp (create i)) n (removeOccupation i n) =
      (Real.sqrt (n i : ℝ) : ℂ) * Complex.exp ((τ * freeEigenvalue ε n : ℝ) : ℂ) := by
  rw [imaginaryTimeEvolveFree, Common.matrixCoeff_diagonalEvolution_comp, matrixCoeff_create]
  by_cases h : n i = 0
  · have hrw : removeOccupation i n = n := by
      ext k
      rcases eq_or_ne k i with rfl | hk
      · rw [removeOccupation_apply_same, h]
      · rw [removeOccupation_apply_ne hk]
    have hne : n ≠ createOccupation i (removeOccupation i n) := by
      rw [hrw]
      intro heq
      have hc := congrArg (fun x : Occupation Mode => x i) heq
      rw [createOccupation_apply_same, h] at hc
      omega
    rw [ite_eq_right hne, h]
    simp
  · have htarget : n = createOccupation i (removeOccupation i n) :=
      (createOccupation_removeOccupation_of_pos h).symm
    have hcoordN : (removeOccupation i n) i + 1 = n i := by
      rw [removeOccupation_apply_same]
      omega
    have hcoord : ((removeOccupation i n) i : ℝ) + 1 = (n i : ℝ) := by
      exact_mod_cast hcoordN
    rw [ite_eq_left htarget, hcoord, mul_comm]

omit [Fintype Mode] in
/-- Mixed matrix coefficients vanish when the annihilation and creation modes differ. -/
private theorem matrixCoeff_imaginaryTimeEvolveFree_comp_create_mul_matrixCoeff_annihilate_of_ne
    {i j : Mode} (h : i ≠ j) (ε : Mode → ℝ) (τ : ℝ) (n k : Occupation Mode) :
    Common.matrixCoeff ((imaginaryTimeEvolveFree ε τ).comp (create j)) n k *
      Common.matrixCoeff (annihilate i) k n = 0 := by
  rw [matrixCoeff_annihilate]
  by_cases hk : k = removeOccupation i n
  · rw [ite_eq_left hk]
    subst k
    rw [imaginaryTimeEvolveFree, Common.matrixCoeff_diagonalEvolution_comp, matrixCoeff_create]
    have hne : createOccupation j (removeOccupation i n) ≠ n := by
      intro heq
      have hc := createOccupation_apply_same j (removeOccupation i n)
      rw [heq, removeOccupation_apply_ne (Ne.symm h)] at hc
      omega
    rw [ite_eq_right (Ne.symm hne), mul_zero, zero_mul]
  · rw [ite_eq_right hk, mul_zero]

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
        rw [matrixCoeff_annihilate, ite_eq_right hk]
      rw [hFdef]
      simp only [Function.uncurry, hval, mul_zero]
  have hcomp : F ∘ g = fun n => (n i : ℂ) *
      Complex.exp ((-β * freeEigenvalue ε n : ℝ) : ℂ) := by
    funext n
    rw [Function.comp_apply, hFdef, hgdef]
    simp only [Function.uncurry]
    rw [matrixCoeff_imaginaryTimeEvolveFree_comp_create_removeOccupation,
      matrixCoeff_annihilate, ite_eq_left rfl, mul_right_comm, sqrt_natCast_mul_self]
  rw [← hginj.summable_iff hvanish, hcomp]
  simpa [boltzmannWeight] using
    Complex.summable_ofReal.mpr
      (summable_particleNumber_boltzmannWeight ε β hpos i)

/-- The Boltzmann-weighted diagonal partition series is summable over `ℂ`. -/
theorem summable_imaginaryTimeEvolveFree_self (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i) :
    Summable (fun n : Occupation Mode =>
      Common.matrixCoeff (imaginaryTimeEvolveFree ε (-β)) n n) := by
  simpa [matrixCoeff_imaginaryTimeEvolveFree_self, boltzmannWeight] using
    Complex.summable_ofReal.mpr (summable_boltzmannWeight ε β hpos)


end
end Bosonic
end SecondQuantization
